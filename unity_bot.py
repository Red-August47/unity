import asyncio
import functools
import hashlib
import io
import os
import re
import shutil
import struct
import tempfile
import time
import zipfile
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from urllib.parse import urlparse, parse_qs

import httpx
import UnityPy
from PIL import Image
from telegram import Update, BotCommand
from telegram.ext import Application, CommandHandler, MessageHandler, filters, ContextTypes
from telegram.error import RetryAfter, TimedOut, NetworkError, BadRequest


# ==========================================================================
# Settings and shared state
# ==========================================================================

MAX_PART = 45 * 1024 * 1024            # Telegram bots can upload up to 50 MB per file
MAX_UNPACKED = 12 * 1024 ** 3          # refuse zips that would unpack to more than this
MIN_SIDE = 9                           # ignore textures 8 px or smaller (placeholders)
BUNDLE_MAGICS = (b"UnityFS", b"UnityWeb", b"UnityRaw")

TOKEN = os.environ["BOT_TOKEN"].strip()   # strip: a pasted secret can carry a hidden newline
ADMIN_CHAT_ID = (os.getenv("ADMIN_CHAT_ID") or "").strip() or None

WORK = Path(tempfile.gettempdir()) / "unitybot"
WORK.mkdir(parents=True, exist_ok=True)

TG_DOWNLOAD_LIMIT = 20 * 1024 * 1024   # Telegram bots can only download up to 20 MB

state = defaultdict(lambda: {
    "loaded": False, "name": "game", "textures": [], "sprites": [], "report": "",
    "busy": False, "split": False, "sprites_on": False,
    "photo_jobs": None, "photo_pos": 0, "photo_sub": 0, "photo_mode": "all",
    "photo_word": "", "seen": set(),
})


def bundle_dir(uid) -> Path:
    return WORK / f"bundles_{uid}"


@dataclass
class Tex:
    name: str
    bundle: str       # path relative to the bundle directory
    pid: int          # path_id of the object inside the bundle
    w: int
    h: int
    kind: str         # "Texture2D" or "Sprite"


# ==========================================================================
# Small helpers
# ==========================================================================

def natural_key(s: str):
    return [int(t) if i % 2 else t.lower() for i, t in enumerate(re.split(r"(\d+)", s))]


def safe_name(name: str) -> str:
    name = re.sub(r'[\\/:*?"<>|\x00-\x1f]', "_", name).strip(" .") or "unnamed"
    return name[:120]


def unique_name(name: str, used: set) -> str:
    if name.lower() not in used:
        used.add(name.lower())
        return name
    root, dot, ext = name.rpartition(".")
    if not dot:
        root, ext = name, ""
    n = 2
    while True:
        cand = f"{root}_{n}" + (f".{ext}" if ext else "")
        if cand.lower() not in used:
            used.add(cand.lower())
            return cand
        n += 1


def is_scene(w: int, h: int) -> bool:
    """A large, wide picture (background / key art) rather than a sprite or icon."""
    return w >= 900 and w >= 1.3 * h


def mb(n: int) -> str:
    return f"{n / 1024 / 1024:.0f} MB"


def _bar(frac: float, width: int = 12) -> str:
    n = max(0, min(width, int(frac * width)))
    return "█" * n + "░" * (width - n)


def _clock(seconds: float) -> str:
    seconds = int(max(0, seconds))
    return f"{seconds // 60}:{seconds % 60:02d}"


def type_name(obj) -> str:
    t = getattr(obj, "type", None)
    return str(getattr(t, "name", None) or t)


def short_err(e: Exception) -> str:
    return f"{type(e).__name__}: {str(e)[:120]}"


# ==========================================================================
# Reading Unity bundles
# ==========================================================================

def is_bundle_file(path: Path) -> bool:
    try:
        with open(path, "rb") as f:
            head = f.read(8)
        return head.startswith(BUNDLE_MAGICS)
    except OSError:
        return False


def find_bundles(root: Path):
    return sorted((p for p in root.rglob("*") if p.is_file() and is_bundle_file(p)),
                  key=lambda p: natural_key(str(p)))


def scan_bundles(root: Path, p: dict):
    """Open every bundle and list its textures. p is a progress dict that the ticker reads."""
    files = find_bundles(root)
    p.update(n=len(files), i=0, tex=0, bad=0)
    textures, sprites = [], []
    types = Counter()
    errors = Counter()
    examples = {}
    for path in files:
        rel = path.relative_to(root).as_posix()
        try:
            env = UnityPy.load(str(path))
            objs = list(env.objects)
        except Exception as e:
            p["bad"] += 1
            key = short_err(e)
            errors[key] += 1
            examples.setdefault(key, rel)
            p["i"] += 1
            continue
        for obj in objs:
            t = type_name(obj)
            types[t] += 1
            if t not in ("Texture2D", "Sprite"):
                continue
            try:
                d = obj.read()
                name = getattr(d, "m_Name", "") or f"{t.lower()}_{obj.path_id}"
                if t == "Texture2D":
                    w, h = int(d.m_Width), int(d.m_Height)
                else:
                    r = getattr(d, "m_Rect", None)
                    w, h = (int(r.width), int(r.height)) if r is not None else (0, 0)
                if 0 < w < MIN_SIDE or 0 < h < MIN_SIDE:
                    continue
                item = Tex(str(name), rel, int(obj.path_id), w, h, t)
                (textures if t == "Texture2D" else sprites).append(item)
                p["tex"] += 1
            except Exception as e:
                key = "reading " + t + ": " + short_err(e)
                errors[key] += 1
                examples.setdefault(key, rel)
        p["i"] += 1
    return textures, sprites, types, errors, examples, len(files)


_cache = {"path": None, "objs": None, "env": None}


def get_object(root: Path, rel: str, pid: int):
    path = str(root / rel)
    if _cache["path"] != path:
        _cache.update(path=None, objs=None, env=None)
        env = UnityPy.load(path)
        _cache.update(path=path, env=env, objs={o.path_id: o for o in env.objects})
    obj = _cache["objs"].get(pid)
    if obj is None:
        raise RuntimeError("object not found in bundle")
    return obj


def render_png(root: Path, t: Tex) -> bytes:
    """Decode one texture/sprite to PNG bytes. Raises on failure."""
    obj = get_object(root, t.bundle, t.pid)
    img = obj.read().image
    if img is None:
        raise RuntimeError("no image data")
    buf = io.BytesIO()
    img.save(buf, format="PNG")
    return buf.getvalue()


# ==========================================================================
# Image conversion and sprite-sheet splitting
# ==========================================================================

def to_jpg(png_bytes: bytes) -> bytes:
    img = Image.open(io.BytesIO(png_bytes))
    if img.mode in ("RGBA", "LA", "PA") or "transparency" in img.info:
        rgba = img.convert("RGBA")
        flat = Image.new("RGB", rgba.size, (255, 255, 255))   # white behind see-through areas
        flat.paste(rgba, mask=rgba.getchannel("A"))
        img = flat
    else:
        img = img.convert("RGB")
    out = io.BytesIO()
    img.save(out, format="JPEG", quality=90)
    return out.getvalue()


def prepare_image(data: bytes):
    """Returns (jpg_or_None, original_bytes). jpg None = must be sent as a file."""
    jpg = None
    try:
        w, h = Image.open(io.BytesIO(data)).size
        # Telegram photo limits: w+h <= 10000, ratio <= 20:1
        if w + h <= 10000 and max(w, h) <= 20 * max(1, min(w, h)):
            jpg = to_jpg(data)
            if len(jpg) > 10 * 1024 * 1024:
                jpg = None
    except Exception:
        jpg = None
    return jpg, data


def _flags(mask):
    w, h = mask.size
    data = mask.tobytes()
    return [data.count(b"\xff", y * w, (y + 1) * w) > 0 for y in range(h)]


def _bands(flags, min_gap=3, min_size=8):
    runs, start = [], None
    for i, f in enumerate(list(flags) + [False]):
        if f and start is None:
            start = i
        elif not f and start is not None:
            runs.append([start, i])
            start = None
    merged = []
    for r in runs:
        if merged and r[0] - merged[-1][1] < min_gap:
            merged[-1][1] = r[1]
        else:
            merged.append(r)
    return [(a, b) for a, b in merged if b - a >= min_size]


def split_frames(png_bytes: bytes, max_pixels: int = 40_000_000):
    """If the image is a sheet of similar-sized frames separated by see-through gaps,
    return each frame as PNG bytes (left-to-right, top-to-bottom). Otherwise None."""
    try:
        img = Image.open(io.BytesIO(png_bytes))
        if img.width * img.height > max_pixels:
            return None
        if not (img.mode in ("RGBA", "LA", "PA") or "transparency" in img.info):
            return None
        img = img.convert("RGBA")
    except Exception:
        return None

    w, h = img.size
    mask = img.getchannel("A").point(lambda v: 255 if v > 16 else 0)
    boxes = []
    for y0, y1 in _bands(_flags(mask)):
        strip = mask.crop((0, y0, w, y1))
        for x0, x1 in _bands(_flags(strip.transpose(Image.Transpose.TRANSPOSE))):
            box = mask.crop((x0, y0, x1, y1)).getbbox()
            if box:
                boxes.append((x0 + box[0], y0 + box[1], x0 + box[2], y0 + box[3]))

    def area(b):
        return (b[2] - b[0]) * (b[3] - b[1])

    if len(boxes) < 2:
        return None
    biggest = max(area(b) for b in boxes)
    big = [b for b in boxes if area(b) >= 0.2 * biggest]
    if len(big) < 2:
        return None
    ws = sorted(b[2] - b[0] for b in big)
    hs = sorted(b[3] - b[1] for b in big)
    mw, mh = ws[len(ws) // 2], hs[len(hs) // 2]
    for b in big:
        if not (0.6 <= (b[2] - b[0]) / mw <= 1.6 and 0.6 <= (b[3] - b[1]) / mh <= 1.6):
            return None

    frames = []
    for b in big:
        out = io.BytesIO()
        img.crop(b).save(out, format="PNG")
        frames.append(out.getvalue())
    return frames


def frame_name(name: str, i: int) -> str:
    base = name.rsplit(".", 1)[0] if name.lower().endswith(".png") else name
    return f"{base}_{i:02d}.png"


def make_items(root: Path, t: Tex, out_name: str, split: bool):
    """-> (items, was_sheet, digest). items = [(name, jpg_or_None, original)]. Raises on failure."""
    png = render_png(root, t)
    digest = hashlib.sha1(png).hexdigest()
    frames = split_frames(png) if split else None
    if not frames:
        jpg, original = prepare_image(png)
        return [(out_name, jpg, original)], False, digest
    items = []
    for i, fr in enumerate(frames, 1):
        jpg, original = prepare_image(fr)
        items.append((frame_name(out_name, i), jpg, original))
    return items, True, digest


# ==========================================================================
# Planning
# ==========================================================================

def plan(st, mode: str, word: str):
    """-> list of (out_name, Tex): large wide pictures first, the rest in natural order."""
    pool = list(st["textures"]) + (list(st["sprites"]) if st["sprites_on"] else [])
    if word:
        pool = [t for t in pool if word in t.name.lower()]
    pool.sort(key=lambda t: natural_key(t.name))
    scenes = [t for t in pool if is_scene(t.w, t.h)]
    if mode == "big":
        pool = scenes
    else:
        ids = {id(t) for t in scenes}
        pool = scenes + [t for t in pool if id(t) not in ids]
    used = set()
    return [(unique_name(safe_name(t.name) + ".png", used), t) for t in pool], len(scenes)


# ==========================================================================
# Zip packing (for /extract)
# ==========================================================================

def build_parts(root: Path, jobs, out_dir: Path, stem: str, split: bool, p: dict):
    report = {"files": 0, "failed": 0, "dups": 0, "too_big": 0, "sheets": 0, "first_error": ""}
    parts = []
    cur = {"zf": None, "count": 0, "idx": 0}
    seen = set()
    p.update(i=0, n=len(jobs))

    def close_part():
        if cur["zf"]:
            cur["zf"].close()
            cur["zf"] = None
            if cur["count"] == 0:
                parts.pop().unlink()

    def new_part():
        close_part()
        cur["idx"] += 1
        path = out_dir / f"{stem}_part{cur['idx']:02d}.zip"
        cur["zf"] = zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED, compresslevel=1)
        cur["count"] = 0
        parts.append(path)

    new_part()
    for out, t in jobs:
        p["i"] += 1
        try:
            png = render_png(root, t)
        except Exception as e:
            report["failed"] += 1
            report["first_error"] = report["first_error"] or short_err(e)
            print(f"[ERROR] {out}: {short_err(e)}")
            continue
        digest = hashlib.sha1(png).hexdigest()
        if digest in seen:
            report["dups"] += 1
            continue
        seen.add(digest)
        writes = [(out, png)]
        if split:
            frames = split_frames(png)
            if frames:
                report["sheets"] += 1
                writes = [(frame_name(out, i), fr) for i, fr in enumerate(frames, 1)]
        for wname, blob in writes:
            if len(blob) > MAX_PART:
                report["too_big"] += 1
                continue
            if cur["count"] > 0 and cur["zf"].fp.tell() + len(blob) > MAX_PART:
                new_part()
            cur["zf"].writestr(wname, blob)
            cur["count"] += 1
            report["files"] += 1
    close_part()
    return parts, report


# ==========================================================================
# Unpacking the download
# ==========================================================================

class LoadError(Exception):
    pass


def unpack(src: Path, root: Path, p: dict):
    """src is a zip of bundles or a single bundle. Fills root with bundle files."""
    shutil.rmtree(root, ignore_errors=True)
    root.mkdir(parents=True)
    if zipfile.is_zipfile(src):
        with zipfile.ZipFile(src) as zf:
            members = [m for m in zf.infolist() if not m.is_dir()]
            total = sum(m.file_size for m in members)
            if total > MAX_UNPACKED:
                raise LoadError(f"The zip would unpack to {total / 1024 ** 3:.1f} GB, which is too much.")
            p.update(n=len(members), i=0)
            root_resolved = root.resolve()
            for m in members:
                parts = [x for x in m.filename.replace("\\", "/").split("/") if x not in ("", ".", "..")]
                p["i"] += 1
                if not parts:
                    continue
                dest = (root / Path(*parts)).resolve()
                if root_resolved not in dest.parents:       # path-traversal guard
                    continue
                dest.parent.mkdir(parents=True, exist_ok=True)
                with zf.open(m) as s, open(dest, "wb") as d:
                    shutil.copyfileobj(s, d, 1024 * 1024)
        src.unlink(missing_ok=True)
        return
    if is_bundle_file(src):
        shutil.move(str(src), root / "single.bundle")
        return
    src.unlink(missing_ok=True)
    raise LoadError("This is neither a zip file nor a Unity bundle (.bundle). "
                    "If you used a link, make sure it is a direct download link.")


# ==========================================================================
# Telegram helpers
# ==========================================================================

def allowed(update: Update) -> bool:
    if not ADMIN_CHAT_ID:
        return True
    ids = set()
    if update.effective_user:
        ids.add(str(update.effective_user.id))
    if update.effective_chat:
        ids.add(str(update.effective_chat.id))
    return ADMIN_CHAT_ID in ids


def guarded(fn):
    @functools.wraps(fn)
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not allowed(update):
            return
        return await fn(update, context)
    return wrapper


def normalize_url(url: str) -> str:
    u = urlparse(url)
    host = u.netloc.lower()
    if "drive.google.com" in host:
        m = re.search(r"/d/([\w-]+)", u.path)
        file_id = m.group(1) if m else parse_qs(u.query).get("id", [None])[0]
        if file_id:
            return f"https://drive.usercontent.google.com/download?id={file_id}&export=download&confirm=t"
    if "dropbox.com" in host:
        if "dl=0" in url:
            return url.replace("dl=0", "dl=1")
        if "dl=1" not in url:
            return url + ("&" if "?" in url else "?") + "dl=1"
    return url


class DownloadError(Exception):
    pass


PROGRESS_EVERY = 4      # seconds between progress updates
STALL_AFTER = 10        # seconds without data before warning that the download may be stuck


async def download(url: str, dest: Path, status_msg):
    """Download a file, showing live progress in status_msg (percent, speed, time left, stall warning)."""
    timeout = httpx.Timeout(30.0, read=120.0)
    t0 = time.monotonic()
    p = {"done": 0, "total": 0, "last": t0, "started": False, "text": ""}

    async def show(text: str):
        if text == p["text"]:
            return
        p["text"] = text
        try:
            await status_msg.edit_text(text)
        except Exception:
            pass

    def progress_text() -> str:
        now = time.monotonic()
        done, total = p["done"], p["total"]
        if not p["started"]:
            return f"⏳ Connecting… {_clock(now - t0)}"
        quiet = now - p["last"]
        speed = done / max(now - t0, 0.1)
        if total:
            frac = done / total
            left = (total - done) / speed if speed > 0 else 0
            text = (f"⬇️ Downloading… {frac:.0%}\n{_bar(frac)}\n"
                    f"{mb(done)} / {mb(total)} · {speed / 1e6:.1f} MB/s\n"
                    f"elapsed {_clock(now - t0)} · about {_clock(left)} left")
        else:
            text = (f"⬇️ Downloading… {mb(done)} · {speed / 1e6:.1f} MB/s\n"
                    f"(total size unknown) · elapsed {_clock(now - t0)}")
        if quiet >= STALL_AFTER:
            text += f"\n⚠️ No data for {int(quiet)}s – it may be stuck (gives up after 2 minutes)"
        return text

    async def ticker():
        while True:
            await asyncio.sleep(PROGRESS_EVERY)
            await show(progress_text())

    task = asyncio.create_task(ticker())
    try:
        async with httpx.AsyncClient(follow_redirects=True, timeout=timeout) as client:
            async with client.stream("GET", url) as r:
                r.raise_for_status()
                if r.headers.get("content-type", "").lower().startswith("text/html"):
                    raise DownloadError(
                        "the link gave a web page instead of the file. Use a direct download link "
                        "(Google Drive: share as 'Anyone with the link'; GitHub: the Release asset link)."
                    )
                p["total"] = int(r.headers.get("content-length") or 0)
                p["started"] = True
                p["last"] = time.monotonic()
                with open(dest, "wb") as out:
                    async for chunk in r.aiter_bytes(1024 * 1024):
                        out.write(chunk)
                        p["done"] += len(chunk)
                        p["last"] = time.monotonic()
    finally:
        task.cancel()
    await show(f"✅ Downloaded {mb(p['done'])} in {_clock(time.monotonic() - t0)}")


async def run_with_ticker(status_msg, fn, p: dict, text_fn):
    """Run a blocking function in a thread while showing live progress from the dict p."""
    last = {"text": ""}

    async def tick():
        while True:
            await asyncio.sleep(PROGRESS_EVERY)
            text = text_fn(p)
            if text != last["text"]:
                last["text"] = text
                try:
                    await status_msg.edit_text(text)
                except Exception:
                    pass

    task = asyncio.create_task(tick())
    try:
        return await asyncio.to_thread(fn)
    finally:
        task.cancel()


def _count_text(label):
    def f(p):
        n, i = p.get("n", 0), p.get("i", 0)
        frac = i / n if n else 0
        extra = f"\n🖼 textures so far: {p['tex']} · unreadable bundles: {p['bad']}" if "tex" in p else ""
        return f"{label} {i}/{n}  {frac:.0%}\n{_bar(frac)}{extra}"
    return f


async def _retry_wait(e):
    wait = e.retry_after
    wait = wait.total_seconds() if hasattr(wait, "total_seconds") else wait
    await asyncio.sleep(wait + 1)


async def send_document_safe(message, path: Path, caption: str) -> bool:
    for _ in range(6):
        try:
            with open(path, "rb") as fh:
                await message.reply_document(
                    document=fh, filename=path.name, caption=caption,
                    read_timeout=600, write_timeout=600, connect_timeout=60,
                )
            return True
        except RetryAfter as e:
            await _retry_wait(e)
        except BadRequest as e:        # BadRequest is a subclass of NetworkError, so it must come first
            print(f"[ERROR] sending {path.name}: {e}")
            return False
        except (TimedOut, NetworkError):
            await asyncio.sleep(5)
        except Exception as e:
            print(f"[ERROR] sending {path.name}: {type(e).__name__}: {e}")
            return False
    return False


async def send_image(message, jpg, original, name):
    """Send as a photo if possible, otherwise as a file. Returns (status, error): ok | skip | stop."""
    caption = name[-1000:]
    filename = name.rsplit("/", 1)[-1]
    err = ""
    if jpg is not None:
        for _ in range(6):
            try:
                await message.reply_photo(photo=io.BytesIO(jpg), caption=caption)
                return "ok", ""
            except RetryAfter as e:
                await _retry_wait(e)
            except BadRequest as e:    # must come before NetworkError (it is a subclass)
                err = str(e)
                break
            except (TimedOut, NetworkError):
                await asyncio.sleep(3)
            except Exception as e:
                err = f"{type(e).__name__}: {e}"
                break
        else:
            return "stop", "Telegram kept timing out / rate limiting"
    if len(original) > 49 * 1024 * 1024:
        return "skip", "file too big for Telegram"
    for _ in range(6):
        try:
            await message.reply_document(document=io.BytesIO(original), filename=filename, caption=caption)
            return "ok", ""
        except RetryAfter as e:
            await _retry_wait(e)
        except BadRequest as e:
            return "skip", str(e)
        except (TimedOut, NetworkError):
            await asyncio.sleep(3)
        except Exception as e:
            return "skip", f"{type(e).__name__}: {e}"
    return "stop", "Telegram kept timing out / rate limiting"


# ==========================================================================
# Loading and scanning
# ==========================================================================

def build_report(st, types, errors, examples, nfiles, bad) -> str:
    big = sum(1 for t in st["textures"] if is_scene(t.w, t.h))
    lines = [
        f"📦 Bundles: {nfiles} found, {nfiles - bad} opened, {bad} failed",
        f"🖼 Textures: {len(st['textures'])} · Sprites: {len(st['sprites'])}"
        + (" (sprites are OFF, see /sprites)" if not st["sprites_on"] and st["sprites"] else ""),
        f"🏞 Large wide pictures (scenes): {big}",
    ]
    if types:
        lines.append("Object types: " + " · ".join(f"{k} {v}" for k, v in types.most_common(8)))
    if errors:
        lines.append("\nProblems:")
        for key, n in errors.most_common(4):
            lines.append(f"• {n}× {key}\n   e.g. {examples.get(key, '?')}")
    if nfiles and not st["textures"]:
        lines.append(
            "\n⚠️ No textures found. If the problems above mention 'version' or 'typetree', "
            "try /unityver 2021.3.0f1 (use your game's Unity version) and /scan again."
        )
    return "\n".join(lines)


async def scan_and_report(update: Update, st, uid):
    root = bundle_dir(uid)
    status = await update.message.reply_text("🔍 Reading bundles…")
    p = {"n": 0, "i": 0, "tex": 0, "bad": 0}
    try:
        textures, sprites, types, errors, examples, nfiles = await run_with_ticker(
            status, lambda: scan_bundles(root, p), p, _count_text("🔍 Reading bundles"))
    except Exception as e:
        print(f"[ERROR] scan failed: {short_err(e)}")
        return await update.message.reply_text(f"❌ Scan failed: {short_err(e)}")
    st.update(textures=textures, sprites=sprites, loaded=nfiles > 0, photo_jobs=None,
              photo_pos=0, photo_sub=0, seen=set())
    if not nfiles:
        return await update.message.reply_text("❌ No Unity bundles found in what you sent.")
    st["report"] = build_report(st, types, errors, examples, nfiles, p["bad"])
    for line in errors:
        print(f"[scan problem] {line} (e.g. {examples.get(line)})")
    text = "✅ Scan finished\n\n" + st["report"]
    if textures or (sprites and st["sprites_on"]):
        text += ("\n\n/photos big – only the large pictures\n/photos – every image, large ones first\n"
                 "/photos <word> – only names containing the word\n/extract – everything as zip parts")
    await update.message.reply_text(text)


async def load_file(update: Update, path: Path, name: str):
    uid = update.effective_user.id
    st = state[uid]
    root = bundle_dir(uid)
    status = await update.message.reply_text("📂 Unpacking…")
    p = {"n": 0, "i": 0}
    try:
        await run_with_ticker(status, lambda: unpack(path, root, p), p, _count_text("📂 Unpacking"))
    except LoadError as e:
        path.unlink(missing_ok=True)
        return await update.message.reply_text(f"❌ {e}")
    except zipfile.BadZipFile:
        path.unlink(missing_ok=True)
        return await update.message.reply_text("❌ The zip file is damaged or incomplete.")
    except Exception as e:
        path.unlink(missing_ok=True)
        print(f"[ERROR] unpack failed: {short_err(e)}")
        return await update.message.reply_text(f"❌ Could not unpack: {short_err(e)}")
    st["name"] = re.sub(r"[^\w.-]", "_", name.rsplit(".", 1)[0])[:40] or "game"
    await scan_and_report(update, st, uid)


async def load_from_url(update: Update, url: str):
    uid = update.effective_user.id
    st = state[uid]
    if st["busy"]:
        return  # silent: ignore extra commands while busy
    st["busy"] = True
    path = WORK / f"{uid}.download"
    try:
        status_msg = await update.message.reply_text("Downloading…")
        try:
            await download(normalize_url(url), path, status_msg)
        except (httpx.HTTPError, DownloadError) as e:
            path.unlink(missing_ok=True)
            why = str(e) if isinstance(e, DownloadError) else type(e).__name__
            return await update.message.reply_text(f"❌ Download failed: {why}")
        name = Path(urlparse(url).path).name or "game.zip"
        await load_file(update, path, name)
    finally:
        st["busy"] = False


# ==========================================================================
# Commands
# ==========================================================================

@guarded
async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        "Unity Bundle Extractor\n\n"
        "1. Zip the folder with the .bundle files (StreamingAssets/aa/StandaloneWindows64)\n"
        "2. Upload the zip somewhere with a direct link (GitHub Release, Google Drive, Dropbox)\n"
        "3. Send /load <link> (or just paste the link)\n"
        "4. Send /photos big\n\n"
        "Commands:\n"
        "• /load <link> – download a zip of bundles (or one .bundle)\n"
        "• /scan – read the bundles again\n"
        "• /types – what was found, and any problems\n"
        "• /photos – send images as photos (large pictures first)\n"
        "• /photos big – only large pictures (backgrounds, scenes)\n"
        "• /photos <word> – only images whose name contains the word\n"
        "• /extract [word] – images as PNG zip parts\n"
        "• /sprites on|off – include Sprite objects too (off by default)\n"
        "• /split on|off – cut sprite sheets into separate frames (off by default)\n"
        "• /unityver <version> – set Unity version if bundles fail to read\n"
        "• /clear – delete the loaded files\n"
        "• /stop – shut down the bot\n\n"
        "Single .bundle files up to 20 MB can also be sent directly; more than one at a time "
        "needs a zip link, because Telegram bots can't download more than 20 MB."
    )


@guarded
async def load_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args:
        return await update.message.reply_text("Usage: /load <direct link to the zip>")
    await load_from_url(update, context.args[0])


@guarded
async def link_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    m = re.search(r"https?://\S+", update.message.text or "")
    if m:
        await load_from_url(update, m.group(0))


@guarded
async def handle_document(update: Update, context: ContextTypes.DEFAULT_TYPE):
    doc = update.message.document
    if not doc:
        return
    if doc.file_size and doc.file_size > TG_DOWNLOAD_LIMIT:
        return await update.message.reply_text(
            f"❌ That file is {mb(doc.file_size)}. Telegram bots can't download files over 20 MB.\n"
            "Upload it to GitHub Releases, Google Drive or Dropbox and send me the link instead."
        )
    uid = update.effective_user.id
    st = state[uid]
    if st["busy"]:
        return  # silent: ignore extra commands while busy
    st["busy"] = True
    try:
        path = WORK / f"{uid}.download"
        tg_file = await doc.get_file()
        await tg_file.download_to_drive(custom_path=path)
        await load_file(update, path, doc.file_name or "game.zip")
    finally:
        st["busy"] = False


@guarded
async def scan_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    st = state[uid]
    if not bundle_dir(uid).exists():
        return await update.message.reply_text("Nothing loaded yet. Use /load <link>.")
    if st["busy"]:
        return  # silent: ignore extra commands while busy
    st["busy"] = True
    try:
        await scan_and_report(update, st, uid)
    finally:
        st["busy"] = False


@guarded
async def types_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    st = state[update.effective_user.id]
    if not st["report"]:
        return await update.message.reply_text("Nothing loaded yet. Use /load <link>.")
    await update.message.reply_text(st["report"])


@guarded
async def photos_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    st = state[uid]
    root = bundle_dir(uid)
    if not st["loaded"] or not root.exists():
        return await update.message.reply_text("Nothing loaded yet. Use /load <link>.")
    if st["busy"]:
        return  # silent: ignore extra commands while busy

    args = [a.lower() for a in context.args]
    mode = "big" if args and args[0] == "big" else "all"
    word = " ".join(args[1:] if mode == "big" else args).strip()

    st["busy"] = True
    try:
        pending = st["photo_jobs"] is not None and st["photo_pos"] < len(st["photo_jobs"])
        fresh = (not pending) or st["photo_mode"] != mode or st["photo_word"] != word
        nbig = 0
        if fresh:
            jobs, nbig = plan(st, mode, word)
            st.update(photo_jobs=jobs, photo_pos=0, photo_sub=0, photo_mode=mode, photo_word=word, seen=set())
        jobs = st["photo_jobs"]
        if not jobs:
            st["photo_jobs"] = None
            return await update.message.reply_text(
                "No large pictures found. Try /photos for everything." if mode == "big" and not word
                else "No matching images found. Check /types."
            )

        if not fresh:
            text = f"Continuing from image {st['photo_pos'] + 1} of {len(jobs)}…"
        elif mode == "big":
            text = f"Sending {len(jobs)} large picture(s) as photos…"
        else:
            text = f"Sending {len(jobs)} image(s) as photos – the {nbig} large pictures come first…"
        await update.message.reply_text(text)

        sent = files = skipped = sheets = dups = 0
        first_error = ""
        while st["photo_pos"] < len(jobs):
            out, t = jobs[st["photo_pos"]]
            try:
                items, was_sheet, digest = await asyncio.to_thread(make_items, root, t, out, st["split"])
            except Exception as e:
                skipped += 1
                first_error = first_error or short_err(e)
                print(f"[ERROR] {out} ({t.bundle}): {short_err(e)}")
                st["photo_pos"] += 1
                st["photo_sub"] = 0
                continue
            if digest in st["seen"]:
                dups += 1
                st["photo_pos"] += 1
                st["photo_sub"] = 0
                continue
            sheets += was_sheet and st["photo_sub"] == 0
            for idx in range(st["photo_sub"], len(items)):
                name, jpg, original = items[idx]
                status, err = await send_image(update.message, jpg, original, name)
                if status == "stop":
                    await update.message.reply_text(
                        f"⚠️ Stopped at image {st['photo_pos'] + 1} of {len(jobs)} ({err}).\n"
                        "Send /photos again to continue."
                    )
                    return
                if status == "ok":
                    sent += 1
                    files += jpg is None
                else:
                    skipped += 1
                    print(f"[ERROR] could not send {name}: {err}")
                st["photo_sub"] = idx + 1
                await asyncio.sleep(0.5)
            st["seen"].add(digest)
            st["photo_pos"] += 1
            st["photo_sub"] = 0
            if sent and sent % 250 < len(items):
                await update.message.reply_text(f"…{st['photo_pos']}/{len(jobs)} done")

        st["photo_jobs"] = None
        st["photo_pos"] = 0
        lines = [f"✅ Done: {sent} image(s) sent."]
        if sheets:
            lines.append(f"✂️ {sheets} sprite sheet(s) were split into separate frames.")
        if files:
            lines.append(f"ℹ️ {files} were sent as files (Telegram wouldn't accept them as photos).")
        if dups:
            lines.append(f"♻️ {dups} identical copies skipped.")
        if skipped:
            lines.append(f"⚠️ {skipped} skipped (could not be decoded or sent). First problem: {first_error or 'see log'}")
        await update.message.reply_text("\n".join(lines))
    finally:
        st["busy"] = False


@guarded
async def extract_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    st = state[uid]
    root = bundle_dir(uid)
    if not st["loaded"] or not root.exists():
        return await update.message.reply_text("Nothing loaded yet. Use /load <link>.")
    if st["busy"]:
        return  # silent: ignore extra commands while busy

    word = " ".join(context.args).strip().lower()
    st["busy"] = True
    out_dir = WORK / f"out_{uid}"
    try:
        jobs, _ = plan(st, "all", word)
        if not jobs:
            return await update.message.reply_text("Nothing matched. Check /types.")
        status = await update.message.reply_text(f"Extracting {len(jobs)} image(s)…")
        shutil.rmtree(out_dir, ignore_errors=True)
        out_dir.mkdir(parents=True)
        p = {"n": len(jobs), "i": 0}
        stem = st["name"] + (f"_{safe_name(word)}" if word else "")
        parts, report = await run_with_ticker(
            status, lambda: build_parts(root, jobs, out_dir, stem, st["split"], p), p, _count_text("🗜 Extracting"))
        if not parts:
            msg = "❌ Nothing could be extracted."
            if report["first_error"]:
                msg += f"\nFirst problem: {report['first_error']}"
            return await update.message.reply_text(msg)

        await update.message.reply_text(f"Sending {len(parts)} zip part(s)…")
        sent = 0
        for i, part in enumerate(parts, 1):
            if await send_document_safe(update.message, part, f"Part {i}/{len(parts)}"):
                sent += 1
            else:
                await update.message.reply_text(f"⚠️ Could not send part {i}.")
            part.unlink(missing_ok=True)

        lines = [f"✅ Done: {report['files']} file(s) in {sent}/{len(parts)} zip part(s)."]
        if report["sheets"]:
            lines.append(f"✂️ {report['sheets']} sprite sheet(s) were split into separate frames.")
        if report["dups"]:
            lines.append(f"♻️ {report['dups']} identical copies skipped.")
        if report["failed"]:
            lines.append(f"⚠️ {report['failed']} could not be decoded. First problem: {report['first_error']}")
        if report["too_big"]:
            lines.append(f"⚠️ {report['too_big']} file(s) skipped (over 45 MB).")
        await update.message.reply_text("\n".join(lines))
    finally:
        st["busy"] = False
        shutil.rmtree(out_dir, ignore_errors=True)


@guarded
async def sprites_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    st = state[update.effective_user.id]
    arg = context.args[0].lower() if context.args else ""
    if arg in ("on", "off"):
        st["sprites_on"] = arg == "on"
        st["photo_jobs"] = None
    await update.message.reply_text(
        f"Sprites are {'ON' if st['sprites_on'] else 'OFF'}.\n"
        "/sprites on – also send Sprite objects (cut-outs from atlases, can repeat what the textures already show)\n"
        "/sprites off – textures only"
    )


@guarded
async def split_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    st = state[update.effective_user.id]
    arg = context.args[0].lower() if context.args else ""
    if arg in ("on", "off"):
        st["split"] = arg == "on"
    await update.message.reply_text(
        f"Sprite-sheet splitting is {'ON' if st['split'] else 'OFF'}.\n"
        "/split on – cut sheets (many frames in one image) into separate images\n"
        "/split off – send every image as it is"
    )


@guarded
async def unityver_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not context.args:
        cur = getattr(UnityPy.config, "FALLBACK_UNITY_VERSION", None)
        return await update.message.reply_text(
            f"Fallback Unity version: {cur or 'not set'}\nUsage: /unityver 2021.3.0f1, then /scan"
        )
    ver = context.args[0].strip()
    if not re.fullmatch(r"\d{4}\.\d+\.\d+[a-z]\d+|\d+\.\d+\.\d+[a-z]?\d*", ver):
        return await update.message.reply_text("That doesn't look like a Unity version, e.g. 2021.3.16f1")
    UnityPy.config.FALLBACK_UNITY_VERSION = ver
    _cache.update(path=None, objs=None, env=None)
    await update.message.reply_text(f"Fallback Unity version set to {ver}. Send /scan to read the bundles again.")


@guarded
async def clear_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    st = state[uid]
    _cache.update(path=None, objs=None, env=None)
    shutil.rmtree(bundle_dir(uid), ignore_errors=True)
    st.update(loaded=False, textures=[], sprites=[], report="", photo_jobs=None, photo_pos=0,
              photo_sub=0, photo_mode="all", photo_word="", seen=set())
    await update.message.reply_text("🗑️ Cleared.")


@guarded
async def stop(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text("Bot is shutting down. Start a new workflow run to use it again.")
    os._exit(0)


async def post_init(application: Application):
    await application.bot.set_my_commands([
        BotCommand("start", "Show usage"),
        BotCommand("load", "Load a zip of bundles from a link"),
        BotCommand("scan", "Read the bundles again"),
        BotCommand("types", "What was found / problems"),
        BotCommand("photos", "Send images as photos (big = large only)"),
        BotCommand("extract", "Images as PNG zip parts"),
        BotCommand("sprites", "Include Sprite objects: on / off"),
        BotCommand("split", "Split sprite sheets: on / off"),
        BotCommand("unityver", "Set Unity version"),
        BotCommand("clear", "Delete the loaded files"),
        BotCommand("stop", "Shut down the bot"),
    ])
    if ADMIN_CHAT_ID:
        try:
            await application.bot.send_message(
                chat_id=int(ADMIN_CHAT_ID), text="✅ Unity Extractor Bot is online and ready."
            )
        except Exception as e:
            print(f"[startup notification failed] {e}")


def main():
    app = (
        Application.builder()
        .token(TOKEN)
        .concurrent_updates(8)
        .connection_pool_size(16)
        .pool_timeout(30)
        .read_timeout(60)
        .write_timeout(600)
        .post_init(post_init)
        .build()
    )
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("load", load_cmd))
    app.add_handler(CommandHandler("scan", scan_cmd))
    app.add_handler(CommandHandler("types", types_cmd))
    app.add_handler(CommandHandler("photos", photos_cmd))
    app.add_handler(CommandHandler("extract", extract_cmd))
    app.add_handler(CommandHandler("sprites", sprites_cmd))
    app.add_handler(CommandHandler("split", split_cmd))
    app.add_handler(CommandHandler("unityver", unityver_cmd))
    app.add_handler(CommandHandler("clear", clear_cmd))
    app.add_handler(CommandHandler("stop", stop))
    app.add_handler(MessageHandler(filters.Document.ALL, handle_document))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND & filters.Regex(r"https?://"), link_message))

    print("Bot started...")
    app.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()

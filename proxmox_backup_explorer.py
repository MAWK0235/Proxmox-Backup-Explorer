#!/usr/bin/env python3
"""
Proxmox Backup Explorer — Cross-Platform ZFS & VZDump Backup Browser (Linux & Windows)
https://github.com/your-username/proxmox-backup-explorer

Features:
- Auto-discovers any encrypted (passphrase) or unencrypted ZFS pool, plus local/network backup folders.
- Imports ZFS pools strictly read-only (-o readonly=on -o cachefile=none) by default.
- Persistent left-hand Action & Live Status Panel with instant cancellation for scans & extractions.
- Auto-deletes incomplete extraction folders on Cancel or Ctrl+C, and locks/exports ZFS pools on exit.
- Smart Views: Photos & Videos gallery (with inline lightbox & HTML5 video player), Largest Files,
  Documents & Configs, and instant search.
- Optional "Danger Zone" Management Mode for pruning old backups and reclaiming local cache space.
"""

import atexit
import hashlib
import http.server
import json
import mimetypes
import os
import platform
import re
import secrets
import shutil
import signal
import socketserver
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
import urllib.parse
import webbrowser

if platform.system() != "Windows":
    import pwd

APP_VERSION = "1.0.0"
IS_WINDOWS = platform.system() == "Windows"
ZFS_ALTROOT = "/mnt/proxmox-zfs-explorer"
CACHE_DIR = os.path.join(tempfile.gettempdir(), "proxmox-backup-explorer-cache")
PREVIEW_DIR = os.path.join(tempfile.gettempdir(), "proxmox-backup-explorer-preview")
SYSTEM_POOL_NAMES = {"rpool", "bpool", "boot-pool", "freenas-boot", "truenas-boot"}

IMAGE_EXTS = {".jpg", ".jpeg", ".png", ".webp", ".gif", ".bmp", ".heic", ".avif"}
VIDEO_EXTS = {".mp4", ".mov", ".webm", ".mkv", ".avi", ".m4v"}
DOC_EXTS = {
    ".pdf", ".doc", ".docx", ".xls", ".xlsx", ".csv", ".txt", ".md",
    ".json", ".yml", ".yaml", ".conf", ".env", ".sql", ".db", ".sqlite",
}

# --- Global Runtime State ---
ACTIVE_SOURCE = None  # {"kind": "zfs_import"|"zfs_mounted"|"folder", "target": str, "label": str, "encrypted": bool, "imported_by_us": bool}
POOL_LOCKED = False
READONLY_MODE = True
DUMP_DIR = None
ARCHIVES = []
INDEX_CACHE = {}       # archive_id -> list of file dicts
EXTRACTED_DIRS = {}    # archive_id -> local extracted folder path

CANCEL_EVENT = threading.Event()
ACTIVE_PARTIAL_EXTRACT = None
ACTIVE_EXTRACT_PROC = None
CLEANUP_EXECUTED = False

TASK_STATUS = {
    "running": False,
    "kind": "",
    "message": "Idle — Ready",
    "percent": 0,
    "error": "",
}

SESSION_TOKEN = secrets.token_urlsafe(24)
SERVER_INSTANCE = None


# --- Privilege & Desktop User Helpers ---
def ensure_privileges():
    if IS_WINDOWS:
        return
    if os.geteuid() != 0:
        caller_user = os.environ.get("USER") or pwd.getpwuid(os.getuid()).pw_name
        target_cmd = [sys.executable] if getattr(sys, "frozen", False) else [sys.executable, os.path.abspath(__file__)]
        env_args = [
            "sudo",
            "--preserve-env=DISPLAY,WAYLAND_DISPLAY,XAUTHORITY,XDG_RUNTIME_DIR,DBUS_SESSION_BUS_ADDRESS",
            f"TARGET_USER={caller_user}",
            *target_cmd,
        ] + sys.argv[1:]
        signal.signal(signal.SIGINT, signal.SIG_IGN)
        res = subprocess.run(env_args)
        sys.exit(res.returncode)


def get_desktop_user_info():
    if IS_WINDOWS:
        return None, None, None, os.path.expanduser("~")
    target = os.environ.get("TARGET_USER") or os.environ.get("SUDO_USER") or "root"
    if target == "root":
        return "root", 0, 0, "/root"
    try:
        pw = pwd.getpwnam(target)
        return target, pw.pw_uid, pw.pw_gid, pw.pw_dir
    except KeyError:
        return "root", 0, 0, "/root"


DESKTOP_USER, DESKTOP_UID, DESKTOP_GID, DESKTOP_HOME = get_desktop_user_info()


def chown_to_desktop_user(path):
    if IS_WINDOWS or DESKTOP_USER in (None, "root"):
        return
    try:
        os.chown(path, DESKTOP_UID, DESKTOP_GID)
        for root, dirs, files in os.walk(path):
            for d in dirs:
                try:
                    os.chown(os.path.join(root, d), DESKTOP_UID, DESKTOP_GID)
                except OSError:
                    pass
            for f in files:
                try:
                    os.chown(os.path.join(root, f), DESKTOP_UID, DESKTOP_GID)
                except OSError:
                    pass
    except OSError:
        pass


def open_browser_as_user(url):
    if IS_WINDOWS or DESKTOP_USER in (None, "root"):
        webbrowser.open(url)
        return
    env = os.environ.copy()
    if "LD_LIBRARY_PATH_ORIG" in env:
        env["LD_LIBRARY_PATH"] = env["LD_LIBRARY_PATH_ORIG"]
    else:
        env.pop("LD_LIBRARY_PATH", None)
    env.setdefault("XDG_RUNTIME_DIR", f"/run/user/{DESKTOP_UID}")
    env.setdefault("DBUS_SESSION_BUS_ADDRESS", f"unix:path=/run/user/{DESKTOP_UID}/bus")
    xauth = os.path.join(DESKTOP_HOME, ".Xauthority")
    if os.path.exists(xauth):
        env.setdefault("XAUTHORITY", xauth)
    try:
        subprocess.Popen(
            ["sudo", "-u", DESKTOP_USER, "xdg-open", url],
            env=env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
    except Exception:
        webbrowser.open(url)


def run_cmd(cmd, input_text=None):
    return subprocess.run(cmd, input=input_text, capture_output=True, text=True)


# --- Partial File Removal & ZFS Lock/Export Cleanup ---
def remove_partial_extraction():
    global ACTIVE_PARTIAL_EXTRACT, ACTIVE_EXTRACT_PROC
    if ACTIVE_EXTRACT_PROC is not None:
        try:
            ACTIVE_EXTRACT_PROC.kill()
            ACTIVE_EXTRACT_PROC.wait(timeout=3)
        except Exception:
            pass
        ACTIVE_EXTRACT_PROC = None

    if ACTIVE_PARTIAL_EXTRACT and os.path.exists(ACTIVE_PARTIAL_EXTRACT):
        print(f"\n[!] Removing incomplete extraction folder: {ACTIVE_PARTIAL_EXTRACT}")
        shutil.rmtree(ACTIVE_PARTIAL_EXTRACT, ignore_errors=True)
        ACTIVE_PARTIAL_EXTRACT = None


def release_active_source(export_pool=True):
    global ACTIVE_SOURCE, POOL_LOCKED, DUMP_DIR, ARCHIVES, INDEX_CACHE
    remove_partial_extraction()

    if ACTIVE_SOURCE and ACTIVE_SOURCE["kind"] in ("zfs_import", "zfs_mounted"):
        pool = ACTIVE_SOURCE["target"]
        should_export = export_pool and ACTIVE_SOURCE.get("imported_by_us", False)
        if should_export:
            print(f"[*] Locking and exporting ZFS pool '{pool}'...")
            zpool_cmd = "zpool.exe" if IS_WINDOWS else "zpool"
            zfs_cmd = "zfs.exe" if IS_WINDOWS else "zfs"
            subprocess.run([zfs_cmd, "unmount", "-a"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            subprocess.run([zfs_cmd, "unload-key", "-r", pool], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            res = subprocess.run([zpool_cmd, "export", pool], capture_output=True, text=True)
            if res.returncode == 0:
                print(f"[+] ZFS pool '{pool}' locked and exported. Safe to unplug drive!")
            else:
                print(f"[!] Warning: Could not export '{pool}': {res.stderr.strip()}")
            if not IS_WINDOWS and os.path.isdir(ZFS_ALTROOT):
                try:
                    os.rmdir(ZFS_ALTROOT)
                except OSError:
                    pass

    ACTIVE_SOURCE = None
    POOL_LOCKED = False
    DUMP_DIR = None
    ARCHIVES = []
    INDEX_CACHE.clear()


def cleanup_and_exit(cleanup_extracted=False):
    global CLEANUP_EXECUTED
    if CLEANUP_EXECUTED:
        return
    CLEANUP_EXECUTED = True

    CANCEL_EVENT.set()
    remove_partial_extraction()

    if os.path.isdir(PREVIEW_DIR):
        shutil.rmtree(PREVIEW_DIR, ignore_errors=True)

    if cleanup_extracted:
        for path in list(EXTRACTED_DIRS.values()):
            if path and os.path.isdir(path):
                print(f"[*] Deleting extracted folder: {path}")
                shutil.rmtree(path, ignore_errors=True)
        EXTRACTED_DIRS.clear()

    release_active_source(export_pool=True)


def handle_sigint(signum, frame):
    print("\n[!] Interrupt received — aborting active tasks, cleaning partial files, and locking ZFS drive...")
    cleanup_and_exit(cleanup_extracted=False)
    os._exit(130)


signal.signal(signal.SIGINT, handle_sigint)
signal.signal(signal.SIGTERM, handle_sigint)
atexit.register(lambda: cleanup_and_exit(cleanup_extracted=False))


# --- Universal ZFS & Folder Source Discovery ---
def discover_sources(include_system=False):
    sources = []
    zpool_cmd = "zpool.exe" if IS_WINDOWS else "zpool"
    zfs_cmd = "zfs.exe" if IS_WINDOWS else "zfs"
    has_zfs = shutil.which(zpool_cmd) is not None

    if has_zfs:
        if not IS_WINDOWS:
            subprocess.run(["udevadm", "trigger", "--subsystem-match=block"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            subprocess.run(["udevadm", "settle", "--timeout=2"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

        # 1. Already-imported ZFS pools
        listed = run_cmd([zpool_cmd, "list", "-H", "-o", "name,size,health"]).stdout.splitlines()
        active_names = set()
        for line in listed:
            parts = line.split("\t")
            if len(parts) < 3:
                continue
            pname, psize, phealth = parts[0].strip(), parts[1].strip(), parts[2].strip()
            active_names.add(pname)
            if not include_system and pname in SYSTEM_POOL_NAMES:
                continue
            enc = run_cmd([zfs_cmd, "get", "-H", "-o", "value", "encryption", pname]).stdout.strip()
            kstat = run_cmd([zfs_cmd, "get", "-H", "-o", "value", "keystatus", pname]).stdout.strip()
            is_enc = enc not in ("", "off", "-")
            sources.append({
                "kind": "zfs_mounted",
                "target": pname,
                "label": pname,
                "detail": f"Active ZFS Pool • {psize} • {phealth}",
                "encrypted": is_enc,
                "locked": is_enc and kstat == "unavailable",
            })

        # 2. Importable external ZFS pools
        scan_cmds = [[zpool_cmd, "import", "-d", "/dev/disk/by-id"], [zpool_cmd, "import"]] if not IS_WINDOWS else [[zpool_cmd, "import"]]
        seen_importable = set()
        for sc in scan_cmds:
            res = run_cmd(sc)
            combined = res.stdout + "\n" + res.stderr
            blocks = re.split(r"(?=^\s*pool:\s*)", combined, flags=re.MULTILINE)
            for blk in blocks:
                pm = re.search(r"^\s*pool:\s*(\S+)", blk, re.MULTILINE)
                if not pm:
                    continue
                pname = pm.group(1)
                if pname in active_names or pname in seen_importable:
                    continue
                if not include_system and pname in SYSTEM_POOL_NAMES:
                    continue
                seen_importable.add(pname)
                sm = re.search(r"^\s*state:\s*(\S+)", blk, re.MULTILINE)
                pstate = sm.group(1) if sm else "ONLINE"
                sources.append({
                    "kind": "zfs_import",
                    "target": pname,
                    "label": pname,
                    "detail": f"External ZFS Drive (Ready to Import) • {pstate}",
                    "encrypted": None,  # Determined after read-only import
                    "locked": False,
                })

    return {"has_zfs": has_zfs, "sources": sources}


def find_dump_directory(root_path):
    """Finds 'dump/' inside a ZFS pool root or dataset, or accepts a folder containing vzdump files directly."""
    if not os.path.isdir(root_path):
        return None
    direct_dump = os.path.join(root_path, "dump")
    if os.path.isdir(direct_dump):
        return direct_dump
    # Check if root_path itself contains vzdump archives
    for fn in os.listdir(root_path):
        if fn.startswith("vzdump-"):
            return root_path
    # Check 1 level deeper (e.g., child ZFS dataset /pool/backups/dump)
    try:
        for child in os.listdir(root_path):
            sub_dump = os.path.join(root_path, child, "dump")
            if os.path.isdir(sub_dump):
                return sub_dump
    except OSError:
        pass
    return root_path


def mount_and_index_active_source():
    global DUMP_DIR, ARCHIVES, POOL_LOCKED
    zfs_cmd = "zfs.exe" if IS_WINDOWS else "zfs"
    kind = ACTIVE_SOURCE["kind"]
    target = ACTIVE_SOURCE["target"]

    if kind == "folder":
        POOL_LOCKED = False
        DUMP_DIR = find_dump_directory(target)
        if not DUMP_DIR or not os.path.isdir(DUMP_DIR):
            raise RuntimeError(f"Directory '{target}' does not exist or is not accessible.")
        ARCHIVES = scan_dump_archives(DUMP_DIR)
        return

    # ZFS pool (zfs_import or zfs_mounted)
    enc = run_cmd([zfs_cmd, "get", "-H", "-o", "value", "encryption", target]).stdout.strip()
    kstat = run_cmd([zfs_cmd, "get", "-H", "-o", "value", "keystatus", target]).stdout.strip()
    is_enc = enc not in ("", "off", "-")
    ACTIVE_SOURCE["encrypted"] = is_enc

    if is_enc and kstat == "unavailable":
        POOL_LOCKED = True
        DUMP_DIR = None
        ARCHIVES = []
        return

    POOL_LOCKED = False
    run_cmd([zfs_cmd, "mount", "-a"])

    if IS_WINDOWS:
        time.sleep(0.8)
        mp = run_cmd([zfs_cmd, "get", "-H", "-o", "value", "mountpoint", target]).stdout.strip()
        if not re.match(r"^[A-Za-z]:", mp):
            ps = run_cmd([
                "powershell", "-NoProfile", "-Command",
                f"(Get-Volume | Where-Object {{ $_.FileSystemLabel -like '*{target}*' }} | Select-Object -First 1).DriveLetter",
            ])
            dl = ps.stdout.strip()
            if dl:
                mp = f"{dl}:\\"
        pool_root = mp
    else:
        mp = run_cmd([zfs_cmd, "get", "-H", "-o", "value", "mountpoint", target]).stdout.strip()
        if mp and mp not in ("none", "legacy") and os.path.isdir(mp):
            pool_root = mp
        else:
            pool_root = os.path.join(ZFS_ALTROOT, target)

    DUMP_DIR = find_dump_directory(pool_root)
    if not DUMP_DIR or not os.path.isdir(DUMP_DIR):
        raise RuntimeError(f"Pool '{target}' is unlocked, but no Proxmox backup directory was found under '{pool_root}'.")
    ARCHIVES = scan_dump_archives(DUMP_DIR)


def activate_source(kind, target, readonly=True):
    global ACTIVE_SOURCE, READONLY_MODE
    release_active_source(export_pool=True)
    READONLY_MODE = readonly

    if kind == "folder":
        target = os.path.abspath(os.path.expanduser(target))
        ACTIVE_SOURCE = {
            "kind": "folder",
            "target": target,
            "label": os.path.basename(target) or target,
            "encrypted": False,
            "imported_by_us": False,
        }
        mount_and_index_active_source()
        return

    zpool_cmd = "zpool.exe" if IS_WINDOWS else "zpool"
    ro_opt = "readonly=on" if readonly else "readonly=off"

    if kind == "zfs_import":
        if IS_WINDOWS:
            res = run_cmd([zpool_cmd, "import", "-f", "-o", ro_opt, "-o", "cachefile=none", target])
        else:
            os.makedirs(ZFS_ALTROOT, exist_ok=True)
            res = run_cmd([zpool_cmd, "import", "-d", "/dev/disk/by-id", "-f", "-o", ro_opt, "-o", "cachefile=none", "-R", ZFS_ALTROOT, target])
            if res.returncode != 0:
                res = run_cmd([zpool_cmd, "import", "-f", "-o", ro_opt, "-o", "cachefile=none", "-R", ZFS_ALTROOT, target])
        if res.returncode != 0:
            raise RuntimeError(f"Failed to import ZFS pool '{target}':\n{res.stderr.strip()}")

        ACTIVE_SOURCE = {
            "kind": "zfs_import",
            "target": target,
            "label": target,
            "encrypted": False,
            "imported_by_us": True,
        }
    else:
        ACTIVE_SOURCE = {
            "kind": "zfs_mounted",
            "target": target,
            "label": target,
            "encrypted": False,
            "imported_by_us": False,
        }

    mount_and_index_active_source()


def switch_pool_readonly_state(new_readonly):
    """Switches an imported ZFS pool between readonly=on and readonly=off for Management Mode."""
    global READONLY_MODE
    if not ACTIVE_SOURCE:
        READONLY_MODE = new_readonly
        return

    if ACTIVE_SOURCE["kind"] == "folder":
        READONLY_MODE = new_readonly
        return

    if not ACTIVE_SOURCE.get("imported_by_us", False):
        # Pre-mounted host pool: respect its current ZFS property
        zfs_cmd = "zfs.exe" if IS_WINDOWS else "zfs"
        ro_val = run_cmd([zfs_cmd, "get", "-H", "-o", "value", "readonly", ACTIVE_SOURCE["target"]]).stdout.strip()
        if not new_readonly and ro_val == "on":
            raise RuntimeError("This pool was pre-mounted read-only by the host OS. Export it first or mount it via Proxmox Backup Explorer to enable write management.")
        READONLY_MODE = new_readonly
        return

    pool = ACTIVE_SOURCE["target"]
    zpool_cmd = "zpool.exe" if IS_WINDOWS else "zpool"
    zfs_cmd = "zfs.exe" if IS_WINDOWS else "zfs"
    ro_opt = "readonly=on" if new_readonly else "readonly=off"

    run_cmd([zfs_cmd, "unmount", "-a"])
    exp = run_cmd([zpool_cmd, "export", pool])
    if exp.returncode != 0:
        run_cmd([zfs_cmd, "mount", "-a"])
        raise RuntimeError(f"Could not switch pool mode because '{pool}' is currently busy:\n{exp.stderr.strip()}")

    if IS_WINDOWS:
        imp = run_cmd([zpool_cmd, "import", "-f", "-o", ro_opt, "-o", "cachefile=none", pool])
    else:
        os.makedirs(ZFS_ALTROOT, exist_ok=True)
        imp = run_cmd([zpool_cmd, "import", "-d", "/dev/disk/by-id", "-f", "-o", ro_opt, "-o", "cachefile=none", "-R", ZFS_ALTROOT, pool])
        if imp.returncode != 0:
            imp = run_cmd([zpool_cmd, "import", "-f", "-o", ro_opt, "-o", "cachefile=none", "-R", ZFS_ALTROOT, pool])

    if imp.returncode != 0:
        raise RuntimeError(f"Failed to re-import '{pool}' with {ro_opt}:\n{imp.stderr.strip()}")

    READONLY_MODE = new_readonly
    mount_and_index_active_source()


# --- Archive Metadata Scanner & Streaming Indexer ---
def human_size(n):
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or unit == "TB":
            return f"{n:.1f} {unit}" if unit in ("GB", "TB") else f"{int(round(n))} {unit}"
        n /= 1024.0
    return f"{n} B"


def scan_dump_archives(dump_dir):
    pat = re.compile(r"^vzdump-(lxc|qemu)-(\d+)-(\d{4})_(\d{2})_(\d{2})-(\d{2})_(\d{2})_(\d{2})\.(tar|vma)(?:\.(zst|gz|lzo|bz2|xz))?$")
    items = []
    if not os.path.isdir(dump_dir):
        return items

    for fn in os.listdir(dump_dir):
        m = pat.match(fn)
        if not m:
            continue
        full = os.path.join(dump_dir, fn)
        try:
            st = os.stat(full)
        except OSError:
            continue
        if st.st_size == 0:
            continue

        btype = m.group(1).upper()
        bid = int(m.group(2))
        bdate = f"{m.group(3)}-{m.group(4)}-{m.group(5)} {m.group(6)}:{m.group(7)}"
        prefix = re.sub(r"\.(tar|vma)(\.(zst|gz|lzo|bz2|xz))?$", "", full)

        friendly = "unnamed"
        log_path = prefix + ".log"
        if os.path.isfile(log_path):
            try:
                with open(log_path, "r", errors="ignore") as lf:
                    for line in lf:
                        nm = re.search(r"(?:CT|VM) Name:\s*(.+)$", line)
                        if nm:
                            friendly = nm.group(1).strip() or "unnamed"
                            break
            except OSError:
                pass

        note = ""
        if os.path.isfile(full + ".notes"):
            try:
                with open(full + ".notes", "r", errors="ignore") as nf:
                    note = nf.readline().strip()
            except OSError:
                pass

        items.append({
            "filename": fn,
            "path": full,
            "type": btype,
            "vmid": bid,
            "name": friendly,
            "date": bdate,
            "size_bytes": st.st_size,
            "size_human": human_size(st.st_size),
            "mtime": int(st.st_mtime),
            "note": note,
            "protected": os.path.exists(full + ".protected"),
        })

    items.sort(key=lambda x: x["filename"], reverse=True)
    for idx, it in enumerate(items):
        it["id"] = idx
    return items


def classify_file(rel_path):
    ext = os.path.splitext(rel_path)[1].lower()
    if ext in IMAGE_EXTS:
        return "image"
    if ext in VIDEO_EXTS:
        return "video"
    if ext in DOC_EXTS:
        return "doc"
    return "other"


def index_archive_worker(arc_id):
    global TASK_STATUS
    CANCEL_EVENT.clear()
    arc = ARCHIVES[arc_id]
    os.makedirs(CACHE_DIR, exist_ok=True)
    cache_key = hashlib.sha256(f"{arc['filename']}:{arc['size_bytes']}:{arc['mtime']}".encode()).hexdigest()[:20]
    cache_file = os.path.join(CACHE_DIR, f"{cache_key}.json")

    if os.path.isfile(cache_file):
        try:
            with open(cache_file, "r", encoding="utf-8") as cf:
                INDEX_CACHE[arc_id] = json.load(cf)
            TASK_STATUS.update({"running": False, "percent": 100, "message": "Loaded cached index."})
            return
        except Exception:
            pass

    if arc["type"] == "QEMU":
        INDEX_CACHE[arc_id] = [{
            "path": arc["filename"],
            "name": arc["filename"],
            "size": arc["size_bytes"],
            "size_human": arc["size_human"],
            "kind": "other",
            "is_vma": True,
        }]
        TASK_STATUS.update({"running": False, "percent": 100, "message": "VM image ready."})
        return

    entries = []
    total_bytes = max(arc["size_bytes"], 1)

    try:
        try:
            import zstandard as zstd  # type: ignore
            with open(arc["path"], "rb") as raw_f:
                dctx = zstd.ZstdDecompressor()
                with dctx.stream_reader(raw_f) as reader:
                    with tarfile.open(fileobj=reader, mode="r|") as tf:
                        count = 0
                        for member in tf:
                            if CANCEL_EVENT.is_set():
                                TASK_STATUS.update({"running": False, "error": "Archive scan cancelled by user.", "message": "Cancelled"})
                                return
                            if not member.isfile():
                                continue
                            clean_p = member.name.lstrip("./")
                            if not clean_p:
                                continue
                            entries.append({
                                "path": clean_p,
                                "name": os.path.basename(clean_p),
                                "size": member.size,
                                "size_human": human_size(member.size),
                                "kind": classify_file(clean_p),
                            })
                            count += 1
                            if count % 250 == 0:
                                pct = min(98, int((raw_f.tell() / total_bytes) * 100))
                                TASK_STATUS.update({"percent": pct, "message": f"Scanning {arc['name']}: {count:,} files indexed ({pct}%)..."})
        except ImportError:
            zstd_bin = "zstd.exe" if IS_WINDOWS else "zstd"
            if shutil.which(zstd_bin):
                proc = subprocess.Popen([zstd_bin, "-dc", arc["path"]], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
                try:
                    with tarfile.open(fileobj=proc.stdout, mode="r|") as tf:
                        count = 0
                        for member in tf:
                            if CANCEL_EVENT.is_set():
                                proc.kill()
                                TASK_STATUS.update({"running": False, "error": "Archive scan cancelled by user.", "message": "Cancelled"})
                                return
                            if not member.isfile():
                                continue
                            clean_p = member.name.lstrip("./")
                            if not clean_p:
                                continue
                            entries.append({
                                "path": clean_p,
                                "name": os.path.basename(clean_p),
                                "size": member.size,
                                "size_human": human_size(member.size),
                                "kind": classify_file(clean_p),
                            })
                            count += 1
                            if count % 400 == 0:
                                TASK_STATUS.update({"percent": 50, "message": f"Scanning {arc['name']}: {count:,} files indexed..."})
                finally:
                    proc.wait()
            else:
                with tarfile.open(arc["path"], mode="r:*") as tf:
                    for member in tf:
                        if CANCEL_EVENT.is_set():
                            TASK_STATUS.update({"running": False, "error": "Archive scan cancelled by user.", "message": "Cancelled"})
                            return
                        if member.isfile():
                            clean_p = member.name.lstrip("./")
                            entries.append({
                                "path": clean_p,
                                "name": os.path.basename(clean_p),
                                "size": member.size,
                                "size_human": human_size(member.size),
                                "kind": classify_file(clean_p),
                            })

        INDEX_CACHE[arc_id] = entries
        try:
            with open(cache_file, "w", encoding="utf-8") as cf:
                json.dump(entries, cf)
        except Exception:
            pass
        TASK_STATUS.update({"running": False, "percent": 100, "message": f"Ready — {len(entries):,} files indexed."})
    except Exception as exc:
        TASK_STATUS.update({"running": False, "error": str(exc), "message": "Scan error"})


def folder_size_bytes(path):
    total = 0
    if not os.path.exists(path):
        return 0
    for root, _, files in os.walk(path):
        for fn in files:
            try:
                total += os.path.getsize(os.path.join(root, fn))
            except OSError:
                pass
    return total


def extract_full_worker(arc_id, dest_base):
    global ACTIVE_PARTIAL_EXTRACT, ACTIVE_EXTRACT_PROC, TASK_STATUS
    CANCEL_EVENT.clear()
    arc = ARCHIVES[arc_id]
    slug_name = re.sub(r"[^A-Za-z0-9._-]", "", arc["name"]) or "machine"
    slug_date = arc["date"].replace(" ", "_").replace(":", "-")
    target_dir = os.path.join(dest_base, f"{arc['type']}{arc['vmid']}-{slug_name}_{slug_date}")

    ACTIVE_PARTIAL_EXTRACT = target_dir

    try:
        os.makedirs(target_dir, exist_ok=True)
        tar_cmd = ["tar", "-xf", arc["path"], "-C", target_dir] if IS_WINDOWS else ["tar", "--zstd", "-xf", arc["path"], "-C", target_dir]
        ACTIVE_EXTRACT_PROC = subprocess.Popen(tar_cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)

        while ACTIVE_EXTRACT_PROC.poll() is None:
            if CANCEL_EVENT.is_set():
                remove_partial_extraction()
                TASK_STATUS.update({"running": False, "error": "Extraction cancelled — incomplete files deleted.", "message": "Cancelled"})
                return
            extracted_now = human_size(folder_size_bytes(target_dir))
            TASK_STATUS.update({"percent": 50, "message": f"Extracting {arc['name']} -> {target_dir} ({extracted_now} written)..."})
            time.sleep(0.5)

        rc = ACTIVE_EXTRACT_PROC.returncode
        stderr_txt = ACTIVE_EXTRACT_PROC.stderr.read() if ACTIVE_EXTRACT_PROC.stderr else ""
        ACTIVE_EXTRACT_PROC = None

        if CANCEL_EVENT.is_set() or rc != 0:
            remove_partial_extraction()
            TASK_STATUS.update({"running": False, "error": f"Extraction failed or cancelled: {stderr_txt.strip()}", "message": "Cancelled"})
            return

        ACTIVE_PARTIAL_EXTRACT = None
        chown_to_desktop_user(target_dir)
        EXTRACTED_DIRS[arc_id] = target_dir

        entries = []
        for root, _, files in os.walk(target_dir):
            for fn in files:
                fp = os.path.join(root, fn)
                rel = os.path.relpath(fp, target_dir).replace("\\", "/")
                try:
                    sz = os.path.getsize(fp)
                except OSError:
                    sz = 0
                entries.append({
                    "path": rel,
                    "name": fn,
                    "size": sz,
                    "size_human": human_size(sz),
                    "kind": classify_file(rel),
                })
        INDEX_CACHE[arc_id] = entries
        TASK_STATUS.update({"running": False, "percent": 100, "message": f"Extracted to {target_dir}"})
    except Exception as exc:
        remove_partial_extraction()
        TASK_STATUS.update({"running": False, "error": str(exc), "message": "Extraction error"})


def resolve_single_file_on_disk(arc_id, rel_path):
    """Safely extracts a single file on demand into PREVIEW_DIR without unpacking the entire archive."""
    safe_rel = os.path.normpath(rel_path).lstrip("/\\")
    if not safe_rel or safe_rel.startswith(".."):
        return None

    if arc_id in EXTRACTED_DIRS:
        base_dir = os.path.realpath(EXTRACTED_DIRS[arc_id])
        candidate = os.path.realpath(os.path.join(base_dir, safe_rel))
        if candidate.startswith(base_dir + os.sep) and os.path.isfile(candidate):
            return candidate

    arc = ARCHIVES[arc_id]
    arc_hash = hashlib.sha256(arc["filename"].encode()).hexdigest()[:12]
    preview_root = os.path.realpath(os.path.join(PREVIEW_DIR, arc_hash))
    cached_file = os.path.realpath(os.path.join(preview_root, safe_rel))
    if not cached_file.startswith(preview_root + os.sep):
        return None
    if os.path.isfile(cached_file):
        return cached_file

    os.makedirs(os.path.dirname(cached_file), exist_ok=True)
    for candidate_tar_path in (f"./{safe_rel}", safe_rel):
        cmd = ["tar", "-xf", arc["path"], "-C", preview_root, candidate_tar_path]
        if not IS_WINDOWS:
            cmd = ["tar", "--zstd", "-xf", arc["path"], "-C", preview_root, candidate_tar_path]
        res = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        if res.returncode == 0 and os.path.isfile(cached_file):
            return cached_file
    return None


# --- Embedded Web UI (Persistent Left Sidebar + Smart Views + Danger Zone) ---
HTML_PAGE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Proxmox Backup Explorer</title>
<style>
  :root {
    --bg: #0b1120; --sidebar: #111827; --panel: #1e293b; --panel2: #334155;
    --border: #334155; --text: #f8fafc; --muted: #94a3b8;
    --accent: #38bdf8; --accent2: #0284c7; --ok: #22c55e; --warn: #f59e0b; --err: #ef4444;
  }
  * { box-sizing: border-box; }
  body { margin: 0; font-family: system-ui, -apple-system, sans-serif; background: var(--bg); color: var(--text); display: flex; min-height: 100vh; }

  /* Persistent Left Action & Status Sidebar */
  aside {
    width: 300px; flex-shrink: 0; background: var(--sidebar); border-right: 1px solid var(--border);
    padding: 20px 16px; display: flex; flex-direction: column; justify-content: space-between; gap: 18px;
    position: sticky; top: 0; height: 100vh; overflow-y: auto;
  }
  .logo { font-size: 1.15rem; font-weight: 800; letter-spacing: -0.01em; display: flex; align-items: center; gap: 8px; }
  .side-box { background: var(--panel); border: 1px solid var(--border); border-radius: 10px; padding: 12px; }
  .side-label { font-size: 0.72rem; text-transform: uppercase; letter-spacing: 0.06em; color: var(--muted); font-weight: 700; margin-bottom: 6px; }
  .badge { display: inline-block; padding: 3px 9px; border-radius: 999px; font-size: 0.76rem; font-weight: 700; }
  .badge-safe { background: rgba(34, 197, 94, 0.16); color: #4ade80; border: 1px solid rgba(34, 197, 94, 0.35); }
  .badge-danger { background: rgba(239, 68, 68, 0.18); color: #fca5a5; border: 1px solid rgba(239, 68, 68, 0.45); }
  .badge-info { background: rgba(56, 189, 248, 0.16); color: var(--accent); border: 1px solid rgba(56, 189, 248, 0.35); }

  .nav-btn {
    width: 100%; text-align: left; background: transparent; color: var(--text); border: 1px solid transparent;
    padding: 10px 12px; border-radius: 8px; cursor: pointer; font-weight: 600; font-size: 0.9rem;
    display: flex; align-items: center; justify-content: space-between; margin-bottom: 4px; transition: 0.15s;
  }
  .nav-btn:hover { background: var(--panel); }
  .nav-btn.active { background: var(--accent2); border-color: var(--accent); color: #fff; }
  .nav-btn.danger-nav { color: #fca5a5; }
  .nav-btn.danger-nav.active { background: #991b1b; border-color: var(--err); color: #fff; }

  .prog-track { width: 100%; height: 8px; background: #0f172a; border-radius: 999px; overflow: hidden; margin: 8px 0; }
  .prog-fill { height: 100%; background: var(--accent); width: 0%; transition: width 0.25s; }

  .btn {
    background: var(--panel2); color: var(--text); border: 1px solid #475569; padding: 8px 14px;
    border-radius: 8px; cursor: pointer; font-weight: 600; font-size: 0.88rem; transition: 0.15s;
  }
  .btn:hover { background: #475569; }
  .btn:disabled { opacity: 0.45; cursor: not-allowed; }
  .btn-primary { background: var(--accent2); border-color: var(--accent); color: #fff; }
  .btn-primary:hover { background: #0369a1; }
  .btn-danger { background: #7f1d1d; border-color: var(--err); color: #fecaca; }
  .btn-danger:hover { background: #991b1b; }

  main { flex: 1; padding: 28px 32px 70px; max-width: 1320px; min-width: 0; }
  .card { background: var(--panel); border: 1px solid var(--border); border-radius: 12px; padding: 20px; margin-bottom: 18px; }
  .grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(275px, 1fr)); gap: 16px; }
  .select-card {
    background: var(--panel); border: 1px solid var(--border); border-radius: 12px; padding: 18px;
    cursor: pointer; transition: 0.15s; display: flex; flex-direction: column; justify-content: space-between;
  }
  .select-card:hover { border-color: var(--accent); transform: translateY(-2px); }

  .tabs { display: flex; flex-wrap: wrap; gap: 8px; margin-bottom: 16px; }
  .tab { padding: 9px 16px; border-radius: 8px; background: var(--panel); border: 1px solid var(--border); cursor: pointer; font-weight: 600; color: var(--muted); }
  .tab.active { background: var(--accent2); color: #fff; border-color: var(--accent); }

  input[type="text"], input[type="password"] {
    background: #0f172a; border: 1px solid #475569; color: var(--text); padding: 10px 14px;
    border-radius: 8px; font-size: 0.94rem; width: 100%;
  }

  .media-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(205px, 1fr)); gap: 14px; }
  .media-item { background: var(--panel); border: 1px solid var(--border); border-radius: 10px; overflow: hidden; display: flex; flex-direction: column; justify-content: space-between; }
  .media-thumb {
    width: 100%; height: 158px; object-fit: cover; background: #020617; cursor: pointer;
    display: flex; align-items: center; justify-content: center; color: var(--accent); font-weight: 700;
  }
  .media-meta { padding: 10px; font-size: 0.82rem; }
  .file-row {
    display: flex; align-items: center; justify-content: space-between; gap: 12px;
    padding: 11px 14px; border-bottom: 1px solid var(--border); font-size: 0.9rem;
  }
  .file-row:hover { background: rgba(56, 189, 248, 0.06); }

  .danger-banner {
    background: linear-gradient(135deg, rgba(127, 29, 29, 0.55), rgba(153, 27, 27, 0.35));
    border: 2px solid var(--err); border-radius: 12px; padding: 20px; margin-bottom: 20px;
  }
  .modal-bg {
    position: fixed; inset: 0; background: rgba(2, 6, 23, 0.86); display: none;
    align-items: center; justify-content: center; z-index: 50; padding: 20px;
  }
  .modal-box { background: var(--panel); border: 1px solid #475569; border-radius: 12px; max-width: 92vw; max-height: 92vh; padding: 18px; overflow: auto; }
  .muted { color: var(--muted); }

  @media (max-width: 860px) {
    body { flex-direction: column; }
    aside { width: 100%; height: auto; position: static; border-right: none; border-bottom: 1px solid var(--border); }
  }
</style>
</head>
<body>

<aside>
  <div style="display:flex; flex-direction:column; gap:16px;">
    <div class="logo">
      <span>Proxmox Backup Explorer</span>
    </div>

    <!-- Active Source & Safety Mode -->
    <div class="side-box">
      <div class="side-label">Active Backup Source</div>
      <div id="sideSourceName" style="font-weight:700; font-size:0.98rem; word-break:break-all;">No drive selected</div>
      <div id="sideSourceDetail" class="muted" style="font-size:0.8rem; margin-top:3px;">Pick a ZFS pool or folder</div>
      <div style="margin-top:8px; display:flex; flex-wrap:wrap; gap:6px;">
        <span id="sideModeBadge" class="badge badge-safe">SAFE READ-ONLY</span>
        <span id="sideEncBadge" class="badge badge-info" style="display:none;"></span>
      </div>
    </div>

    <!-- Live Action & Progress Monitor -->
    <div class="side-box" id="sideStatusBox">
      <div style="display:flex; justify-content:space-between; align-items:center;">
        <div class="side-label" style="margin:0;">Live Status</div>
        <span id="sidePct" style="font-size:0.78rem; color:var(--accent); font-weight:700;"></span>
      </div>
      <div id="sideTaskMsg" style="font-size:0.84rem; margin-top:6px; line-height:1.35;">Idle — Ready</div>
      <div id="sideProgWrap" style="display:none;">
        <div class="prog-track"><div id="sideProgFill" class="prog-fill"></div></div>
        <button class="btn btn-danger" style="width:100%; margin-top:6px; padding:7px;" onclick="cancelOngoingTask()">
          Cancel Ongoing Action
        </button>
      </div>
    </div>

    <!-- Navigation -->
    <div>
      <div class="side-label" style="padding-left:4px;">Navigation</div>
      <button id="navSources" class="nav-btn active" onclick="showSourcesView()">Switch Drive / Pool</button>
      <button id="navMachines" class="nav-btn" style="display:none;" onclick="showMachinesView()">Machines &amp; Snapshots</button>
      <button id="navManage" class="nav-btn danger-nav" style="display:none;" onclick="showManageView()">Cleanup &amp; Management</button>
    </div>
  </div>

  <!-- Bottom Eject Controls -->
  <div style="display:flex; flex-direction:column; gap:8px;">
    <button id="btnEjectSource" class="btn" style="display:none; width:100%;" onclick="ejectCurrentSource()">Lock &amp; Eject Current Pool</button>
    <button class="btn btn-danger" style="width:100%;" onclick="shutdownApp()">Lock All &amp; Exit App</button>
  </div>
</aside>

<main>
  <!-- 1. Source Picker View (ZFS Pools + Custom Folder) -->
  <div id="sourcesView">
    <div style="display:flex; flex-wrap:wrap; justify-content:space-between; align-items:center; gap:12px; margin-bottom:14px;">
      <div>
        <h2 style="margin:0;">Select Backup Drive or Folder</h2>
        <p class="muted" style="margin:4px 0 0;">Supports encrypted ZFS drives (passphrase), unencrypted ZFS pools, or any local/network backup folder.</p>
      </div>
      <div style="display:flex; align-items:center; gap:12px;">
        <label style="font-size:0.85rem; color:var(--muted); cursor:pointer;">
          <input type="checkbox" id="chkShowSysPools" onchange="loadSources()"> Show OS system pools
        </label>
        <button class="btn btn-primary" onclick="loadSources()">Rescan Drives</button>
      </div>
    </div>

    <div id="sourcesGrid" class="grid" style="margin-bottom:22px;"></div>

    <div class="card">
      <h3 style="margin-top:0;">Or Open Any Local / Network Backup Folder</h3>
      <p class="muted" style="font-size:0.9rem; margin-top:0;">Point directly to an already-mounted NFS/SMB share, ext4/NTFS USB drive, or local directory containing <code>vzdump-*.tar.zst</code> backups.</p>
      <div style="display:flex; gap:10px; flex-wrap:wrap;">
        <input type="text" id="customFolderInput" style="flex:1; min-width:260px;" placeholder="/mnt/backups/dump  or  D:\ProxmoxBackups\dump">
        <button class="btn btn-primary" onclick="openCustomFolder()">Open Folder</button>
      </div>
    </div>
  </div>

  <!-- 2. Passphrase Unlock View (Shown only for locked encrypted ZFS pools) -->
  <div id="unlockView" class="card" style="max-width:480px; margin:40px auto; display:none;">
    <h2 style="margin-top:0;">Decrypt ZFS Backup Drive</h2>
    <p class="muted">Pool <strong id="unlockPoolName"></strong> is encrypted. Enter its passphrase to unlock and mount in safe read-only mode.</p>
    <input type="password" id="passInput" placeholder="ZFS encryption passphrase..." onkeydown="if(event.key==='Enter')submitPassphrase()">
    <div id="unlockErr" style="color:var(--err); margin-top:10px; font-size:0.9rem;"></div>
    <div style="display:flex; gap:10px; margin-top:14px;">
      <button class="btn btn-primary" style="flex:1;" onclick="submitPassphrase()">Unlock Drive</button>
      <button class="btn" onclick="ejectCurrentSource()">Cancel</button>
    </div>
  </div>

  <!-- 3. Machine Picker View -->
  <div id="machinesView" style="display:none;">
    <h2 style="margin-top:0; margin-bottom:6px;">Select a Machine</h2>
    <p class="muted" style="margin-top:0;">Choose any container or VM to browse its photos, videos, largest files, or extract a copy.</p>
    <div id="machinesGrid" class="grid"></div>
  </div>

  <!-- 4. Snapshots View for Selected Machine -->
  <div id="snapshotsView" style="display:none;">
    <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom:14px;">
      <h2 id="snapMachineTitle" style="margin:0;"></h2>
      <button class="btn" onclick="showMachinesView()">Back to Machines</button>
    </div>
    <div id="snapshotsList"></div>
  </div>

  <!-- 5. Smart File Explorer View -->
  <div id="explorerView" style="display:none;">
    <div class="card" style="display:flex; flex-wrap:wrap; justify-content:space-between; align-items:center; gap:12px;">
      <div>
        <h2 id="expTitle" style="margin:0;"></h2>
        <div id="expSub" class="muted" style="font-size:0.88rem; margin-top:4px;"></div>
      </div>
      <div style="display:flex; gap:10px;">
        <button class="btn" onclick="promptFullExtract(CURRENT_ARC_ID)">Extract Full Backup...</button>
        <button class="btn" onclick="backToSnapshots()">Change Snapshot</button>
      </div>
    </div>

    <div class="tabs">
      <button class="tab active" data-tab="media" onclick="switchTab('media')">Photos &amp; Videos</button>
      <button class="tab" data-tab="largest" onclick="switchTab('largest')">Largest Files</button>
      <button class="tab" data-tab="docs" onclick="switchTab('docs')">Documents &amp; Configs</button>
      <button class="tab" data-tab="all" onclick="switchTab('all')">All Files / Search</button>
    </div>

    <div style="margin-bottom:16px;">
      <input type="text" id="searchBox" placeholder="Search by filename or folder (e.g. immich, .mp4, world, config)..." oninput="debouncedLoadFiles()">
    </div>

    <div id="filesContainer"></div>
    <div style="margin-top:18px; text-align:center;">
      <button id="loadMoreBtn" class="btn" style="display:none;" onclick="loadMoreFiles()">Load More</button>
    </div>
  </div>

  <!-- 6. Storage Cleanup & File Management ("Danger Zone") -->
  <div id="manageView" style="display:none;">
    <div class="danger-banner">
      <h2 style="margin-top:0; color:#fecaca;">&#9888; DANGER ZONE — STORAGE CLEANUP &amp; FILE MANAGEMENT</h2>
      <p style="font-size:1rem; line-height:1.5; margin-bottom:10px;">
        <strong>ARE YOU SURE?</strong> Deleting backup archives, pruning old snapshots, or modifying files on your backup drive is
        <strong>permanent and irreversible</strong>. Once deleted, data cannot be recovered.
      </p>
      <p style="font-size:1.02rem; font-weight:700; color:#fde047; margin:0 0 14px;">
        DISCLAIMER: If you delete critical backups or damage anything on your drive, it is NOT MAWK's fault!
      </p>

      <div id="mgmtLockBox">
        <label style="display:flex; align-items:center; gap:10px; cursor:pointer; margin-bottom:12px;">
          <input type="checkbox" id="chkAcceptRisk">
          <span>I understand that deletions are permanent and <strong>NOT MAWK's fault</strong>.</span>
        </label>
        <button class="btn btn-danger" onclick="enableManagementMode()">Unlock Management Mode (Read-Write)</button>
      </div>

      <div id="mgmtActiveBox" style="display:none; align-items:center; justify-content:space-between; flex-wrap:wrap; gap:12px;">
        <span class="badge badge-danger">WRITE ACCESS ENABLED — PROCEED WITH CAUTION</span>
        <button class="btn" onclick="disableManagementMode()">Return to Safe Read-Only Mode</button>
      </div>
    </div>

    <!-- Local Disk Cache & Extracted Folders Cleanup -->
    <div class="card">
      <h3 style="margin-top:0;">Local Workstation Cache &amp; Extracted Folders</h3>
      <p class="muted" style="font-size:0.9rem; margin-top:0;">Reclaim space on your local computer's SSD without touching your external backup drive.</p>
      <div style="display:flex; flex-wrap:wrap; gap:12px; align-items:center;">
        <button class="btn" onclick="cleanLocalData('cache')">Clear Preview &amp; Index Cache (<span id="cacheSizeLbl">0 B</span>)</button>
        <button class="btn btn-danger" id="btnCleanExtracted" style="display:none;" onclick="cleanLocalData('extracted')">Delete Locally Extracted Backup Folders (<span id="extCountLbl">0</span>)</button>
      </div>
    </div>

    <!-- Backup Archive Pruning Table -->
    <div class="card">
      <div style="display:flex; flex-wrap:wrap; justify-content:space-between; align-items:center; gap:12px; margin-bottom:14px;">
        <div>
          <h3 style="margin:0;">Backup Archives on Drive (<span id="mgmtTotalCount">0</span>)</h3>
          <div class="muted" style="font-size:0.86rem;">Deleting an archive also removes its companion <code>.log</code> and <code>.notes</code> files.</div>
        </div>
        <div style="display:flex; flex-wrap:wrap; gap:8px;">
          <button class="btn" onclick="selectOldBackups(30)">Select Unprotected &gt; 30 Days</button>
          <button class="btn" onclick="clearMgmtSelection()">Clear Selection</button>
          <button class="btn btn-danger" id="btnDeleteSelected" disabled onclick="deleteSelectedBackups()">Delete Selected (<span id="selCountLbl">0</span>)</button>
        </div>
      </div>

      <div style="margin-bottom:12px;">
        <label style="font-size:0.85rem; color:var(--muted); cursor:pointer;">
          <input type="checkbox" id="chkAllowProtected"> Allow deleting Proxmox <code>.protected</code> backups (off by default)
        </label>
      </div>

      <div id="mgmtArchivesList"></div>
    </div>
  </div>
</main>

<!-- Media Lightbox Modal -->
<div id="mediaModal" class="modal-bg" onclick="if(event.target===this)closeModal()">
  <div class="modal-box">
    <div style="display:flex; justify-content:space-between; align-items:center; gap:16px; margin-bottom:12px;">
      <strong id="modalTitle" style="word-break:break-all;"></strong>
      <div style="display:flex; gap:8px;">
        <a id="modalDownload" class="btn btn-primary" download>Save File</a>
        <button class="btn" onclick="closeModal()">Close</button>
      </div>
    </div>
    <div id="modalBody" style="text-align:center;"></div>
  </div>
</div>

<script>
const TOKEN = new URLSearchParams(window.location.search).get("token") || "";
let APP_STATE = null;
let SELECTED_MACHINE_KEY = null;
let CURRENT_ARC_ID = null;
let CURRENT_TAB = "media";
let CURRENT_OFFSET = 0;
let SEARCH_TIMER = null;
let SELECTED_FOR_DELETE = new Set();

async function api(path, opts = {}) {
  const sep = path.includes("?") ? "&" : "?";
  const res = await fetch(`${path}${sep}token=${encodeURIComponent(TOKEN)}`, opts);
  return res.json();
}

function fileUrl(arcId, filePath, download = 0) {
  return `/api/stream?token=${encodeURIComponent(TOKEN)}&archive_id=${arcId}&path=${encodeURIComponent(filePath)}&download=${download}`;
}

function setActiveNav(id) {
  document.querySelectorAll(".nav-btn").forEach(b => b.classList.remove("active"));
  const el = document.getElementById(id);
  if (el) el.classList.add("active");
}

function hideAllViews() {
  ["sourcesView", "unlockView", "machinesView", "snapshotsView", "explorerView", "manageView"].forEach(id => {
    document.getElementById(id).style.display = "none";
  });
}

function updateSidebar(st) {
  const src = st.source;
  const modeBadge = document.getElementById("sideModeBadge");
  const encBadge = document.getElementById("sideEncBadge");

  if (st.readonly) {
    modeBadge.className = "badge badge-safe";
    modeBadge.textContent = "SAFE READ-ONLY";
  } else {
    modeBadge.className = "badge badge-danger";
    modeBadge.textContent = "DANGER: READ-WRITE";
  }

  if (!src) {
    document.getElementById("sideSourceName").textContent = "No source selected";
    document.getElementById("sideSourceDetail").textContent = "Pick a ZFS pool or folder";
    encBadge.style.display = "none";
    document.getElementById("navMachines").style.display = "none";
    document.getElementById("navManage").style.display = "none";
    document.getElementById("btnEjectSource").style.display = "none";
  } else {
    document.getElementById("sideSourceName").textContent = src.label;
    document.getElementById("sideSourceDetail").textContent = src.kind === "folder" ? src.target : `${st.archives.length} backup(s)`;
    encBadge.style.display = "inline-block";
    if (src.kind === "folder") {
      encBadge.textContent = "Local / Network Folder";
    } else if (src.encrypted) {
      encBadge.textContent = st.locked ? "Encrypted • Locked" : "Encrypted • Unlocked";
    } else {
      encBadge.textContent = "Unencrypted ZFS";
    }
    document.getElementById("navMachines").style.display = st.locked ? "none" : "flex";
    document.getElementById("navManage").style.display = st.locked ? "none" : "flex";
    document.getElementById("btnEjectSource").style.display = (src.kind === "zfs_import" || src.kind === "zfs_mounted") ? "block" : "none";
  }

  // Live Task Monitor
  const t = st.task || {};
  document.getElementById("sideTaskMsg").textContent = t.message || "Idle — Ready";
  const wrap = document.getElementById("sideProgWrap");
  if (t.running) {
    wrap.style.display = "block";
    document.getElementById("sideProgFill").style.width = `${t.percent || 15}%`;
    document.getElementById("sidePct").textContent = `${t.percent || 0}%`;
  } else {
    wrap.style.display = "none";
    document.getElementById("sidePct").textContent = "";
  }
}

async function refreshStatus() {
  APP_STATE = await api("/api/status");
  updateSidebar(APP_STATE);
  return APP_STATE;
}

// --- 1. Source Discovery & Selection ---
async function showSourcesView() {
  setActiveNav("navSources");
  hideAllViews();
  document.getElementById("sourcesView").style.display = "block";
  await loadSources();
}

async function loadSources() {
  const showSys = document.getElementById("chkShowSysPools").checked ? 1 : 0;
  const data = await api(`/api/sources?include_system=${showSys}`);
  const grid = document.getElementById("sourcesGrid");
  grid.innerHTML = "";

  if (!data.sources || data.sources.length === 0) {
    grid.innerHTML = `<div class="card muted" style="grid-column:1/-1;">
      No external or unmounted ZFS backup pools were detected automatically.
      Plug in your ZFS USB drive and click <strong>Rescan Drives</strong>, or open a local/network folder below.
    </div>`;
    return;
  }

  for (const s of data.sources) {
    const card = document.createElement("div");
    card.className = "select-card";
    card.onclick = () => selectSource(s.kind, s.target);
    const tag = s.kind === "zfs_import" ? "External ZFS Drive" : "Mounted ZFS Pool";
    card.innerHTML = `
      <div>
        <div style="display:flex; justify-content:space-between; align-items:center; gap:8px;">
          <span class="badge badge-info">${tag}</span>
          ${s.encrypted === true ? '<span class="badge" style="background:#78350f;color:#fde68a;">Encrypted</span>' : ''}
          ${s.encrypted === false ? '<span class="badge badge-safe">Unencrypted</span>' : ''}
        </div>
        <h3 style="margin:12px 0 6px;">${s.label}</h3>
      </div>
      <div class="muted" style="font-size:0.84rem;">${s.detail}</div>
    `;
    grid.appendChild(card);
  }
}

async function openCustomFolder() {
  const p = document.getElementById("customFolderInput").value.trim();
  if (!p) return;
  await selectSource("folder", p);
}

async function selectSource(kind, target) {
  document.getElementById("sideTaskMsg").textContent = `Connecting to ${target}...`;
  const res = await api("/api/select_source", {
    method: "POST",
    headers: {"Content-Type": "application/json"},
    body: JSON.stringify({kind, target, readonly: true})
  });
  if (!res.ok) {
    alert(res.error || "Could not open backup source.");
    await refreshStatus();
    return;
  }
  const st = await refreshStatus();
  if (st.locked) {
    hideAllViews();
    document.getElementById("unlockPoolName").textContent = target;
    document.getElementById("unlockErr").textContent = "";
    document.getElementById("unlockView").style.display = "block";
    document.getElementById("passInput").focus();
  } else {
    showMachinesView();
  }
}

async function submitPassphrase() {
  const pw = document.getElementById("passInput").value;
  document.getElementById("unlockErr").textContent = "";
  const res = await api("/api/unlock", {
    method: "POST",
    headers: {"Content-Type": "application/json"},
    body: JSON.stringify({passphrase: pw})
  });
  if (!res.ok) {
    document.getElementById("unlockErr").textContent = res.error || "Incorrect passphrase.";
    return;
  }
  document.getElementById("passInput").value = "";
  await refreshStatus();
  showMachinesView();
}

async function ejectCurrentSource() {
  await api("/api/eject_source", {method: "POST"});
  SELECTED_MACHINE_KEY = null;
  CURRENT_ARC_ID = null;
  await refreshStatus();
  showSourcesView();
}

// --- 2. Machines & Snapshots ---
function showMachinesView() {
  SELECTED_MACHINE_KEY = null;
  CURRENT_ARC_ID = null;
  setActiveNav("navMachines");
  hideAllViews();

  const grid = document.getElementById("machinesGrid");
  grid.innerHTML = "";
  if (!APP_STATE.archives || APP_STATE.archives.length === 0) {
    grid.innerHTML = `<div class="card muted" style="grid-column:1/-1;">No Proxmox backup archives (<code>vzdump-*.tar.zst</code> or <code>.vma.zst</code>) were found on this source.</div>`;
    document.getElementById("machinesView").style.display = "block";
    return;
  }

  const groups = {};
  for (const a of APP_STATE.archives) {
    const key = `${a.type}:${a.vmid}:${a.name}`;
    if (!groups[key]) groups[key] = {key, type: a.type, vmid: a.vmid, name: a.name, items: []};
    groups[key].items.push(a);
  }
  const sorted = Object.values(groups).sort((a, b) => a.vmid - b.vmid);
  for (const g of sorted) {
    const latest = g.items[0];
    const div = document.createElement("div");
    div.className = "select-card";
    div.onclick = () => openMachine(g.key);
    div.innerHTML = `
      <div>
        <div style="display:flex; justify-content:space-between; align-items:center;">
          <span class="badge badge-info">${g.type} ${g.vmid}</span>
          <span class="muted" style="font-size:0.82rem;">${g.items.length} backup(s)</span>
        </div>
        <h3 style="margin:12px 0 6px;">${g.name}</h3>
      </div>
      <div class="muted" style="font-size:0.84rem; margin-top:10px;">
        Latest: ${latest.date} &bull; <strong>${latest.size_human}</strong>
      </div>
    `;
    grid.appendChild(div);
  }
  document.getElementById("machinesView").style.display = "block";
}

function openMachine(key) {
  SELECTED_MACHINE_KEY = key;
  setActiveNav("navMachines");
  hideAllViews();

  const snaps = APP_STATE.archives.filter(a => `${a.type}:${a.vmid}:${a.name}` === key);
  document.getElementById("snapMachineTitle").textContent = `${snaps[0].type} ${snaps[0].vmid} — ${snaps[0].name}`;

  const list = document.getElementById("snapshotsList");
  list.innerHTML = "";
  for (const s of snaps) {
    const card = document.createElement("div");
    card.className = "card";
    card.style.display = "flex";
    card.style.flexWrap = "wrap";
    card.style.justifyContent = "space-between";
    card.style.alignItems = "center";
    card.style.gap = "12px";
    const badges = `${s.protected ? '<span class="badge" style="background:#78350f;color:#fde68a;">Protected</span>' : ''} ${s.note ? `<span class="muted">${s.note}</span>` : ''}`;
    card.innerHTML = `
      <div>
        <div style="font-size:1.05rem; font-weight:700;">${s.date} &nbsp; <span class="badge badge-info">${s.size_human}</span></div>
        <div style="margin-top:6px; font-size:0.85rem;">${badges || '<span class="muted">' + s.filename + '</span>'}</div>
      </div>
      <div style="display:flex; gap:10px;">
        <button class="btn btn-primary" onclick="openSnapshot(${s.id})">Browse Photos, Videos &amp; Files</button>
        <button class="btn" onclick="promptFullExtract(${s.id})">Extract Full Backup...</button>
      </div>
    `;
    list.appendChild(card);
  }
  document.getElementById("snapshotsView").style.display = "block";
}

function backToSnapshots() {
  CURRENT_ARC_ID = null;
  openMachine(SELECTED_MACHINE_KEY);
}

// --- 3. Cancellable Background Tasks (Scan & Extract) ---
async function pollTask() {
  while (true) {
    const st = await refreshStatus();
    const t = st.task;
    if (!t.running) {
      if (t.error) {
        alert(t.error);
        return false;
      }
      return true;
    }
    await new Promise(r => setTimeout(r, 400));
  }
}

async function cancelOngoingTask() {
  await api("/api/cancel_task", {method: "POST"});
}

async function openSnapshot(arcId) {
  CURRENT_ARC_ID = arcId;
  await api("/api/open_snapshot", {
    method: "POST",
    headers: {"Content-Type": "application/json"},
    body: JSON.stringify({archive_id: arcId})
  });
  const ok = await pollTask();
  if (!ok) {
    backToSnapshots();
    return;
  }
  hideAllViews();
  const arc = APP_STATE.archives[arcId];
  document.getElementById("expTitle").textContent = `${arc.name} (${arc.date})`;
  document.getElementById("expSub").textContent = `Archive size: ${arc.size_human} — Click any photo/video to preview, or Save File to extract individual items.`;
  document.getElementById("explorerView").style.display = "block";
  switchTab("media");
}

async function promptFullExtract(arcId) {
  const defaultPath = APP_STATE.default_extract_dir || "";
  const dest = prompt("Enter destination folder path to extract this backup into:\n(Click 'Cancel Ongoing Action' in the left panel or press Ctrl+C to abort & delete partial files)", defaultPath);
  if (!dest) return;

  await api("/api/extract_full", {
    method: "POST",
    headers: {"Content-Type": "application/json"},
    body: JSON.stringify({archive_id: arcId, dest_dir: dest})
  });
  const ok = await pollTask();
  if (ok) {
    await refreshStatus();
    if (CURRENT_ARC_ID === arcId) loadFiles(true);
  }
}

// --- 4. Smart File Explorer Tabs ---
function switchTab(tab) {
  CURRENT_TAB = tab;
  document.querySelectorAll(".tab").forEach(el => el.classList.toggle("active", el.dataset.tab === tab));
  loadFiles(true);
}

function debouncedLoadFiles() {
  clearTimeout(SEARCH_TIMER);
  SEARCH_TIMER = setTimeout(() => loadFiles(true), 220);
}

async function loadFiles(reset = false) {
  if (reset) CURRENT_OFFSET = 0;
  const q = document.getElementById("searchBox").value;
  const data = await api(`/api/files?archive_id=${CURRENT_ARC_ID}&tab=${CURRENT_TAB}&q=${encodeURIComponent(q)}&offset=${CURRENT_OFFSET}&limit=90`);
  const container = document.getElementById("filesContainer");
  if (reset) container.innerHTML = "";

  if (reset && data.items.length === 0) {
    container.innerHTML = `<div class="card muted">No matching files found in this category. Try switching to <strong>Largest Files</strong> or <strong>All Files / Search</strong>.</div>`;
    document.getElementById("loadMoreBtn").style.display = "none";
    return;
  }

  if (CURRENT_TAB === "media") {
    let grid = container.querySelector(".media-grid");
    if (!grid) {
      grid = document.createElement("div");
      grid.className = "media-grid";
      container.appendChild(grid);
    }
    for (const f of data.items) {
      const item = document.createElement("div");
      item.className = "media-item";
      const url = fileUrl(CURRENT_ARC_ID, f.path, 0);
      const dlUrl = fileUrl(CURRENT_ARC_ID, f.path, 1);
      const thumb = f.kind === "image"
        ? `<img class="media-thumb" loading="lazy" src="${url}" onclick="openLightbox(${CURRENT_ARC_ID}, '${f.path.replace(/'/g, "\\'")}', 'image')">`
        : `<div class="media-thumb" onclick="openLightbox(${CURRENT_ARC_ID}, '${f.path.replace(/'/g, "\\'")}', 'video')">&#9654; VIDEO (${f.size_human})</div>`;
      item.innerHTML = `
        ${thumb}
        <div class="media-meta">
          <div style="font-weight:600; white-space:nowrap; overflow:hidden; text-overflow:ellipsis;" title="${f.path}">${f.name}</div>
          <div style="display:flex; justify-content:space-between; align-items:center; margin-top:6px;">
            <span class="muted">${f.size_human}</span>
            <a class="btn" style="padding:4px 8px; font-size:0.78rem; text-decoration:none;" href="${dlUrl}" download>Save</a>
          </div>
        </div>
      `;
      grid.appendChild(item);
    }
  } else {
    let card = container.querySelector(".card");
    if (!card) {
      card = document.createElement("div");
      card.className = "card";
      card.style.padding = "0";
      container.appendChild(card);
    }
    for (const f of data.items) {
      const row = document.createElement("div");
      row.className = "file-row";
      const dlUrl = fileUrl(CURRENT_ARC_ID, f.path, 1);
      const previewBtn = (f.kind === "image" || f.kind === "video")
        ? `<button class="btn" style="padding:5px 10px;" onclick="openLightbox(${CURRENT_ARC_ID}, '${f.path.replace(/'/g, "\\'")}', '${f.kind}')">Preview</button>`
        : "";
      row.innerHTML = `
        <div style="min-width:0; flex:1;">
          <div style="font-weight:600; word-break:break-all;">${f.name}</div>
          <div class="muted" style="font-size:0.8rem; word-break:break-all;">/${f.path}</div>
        </div>
        <div style="display:flex; align-items:center; gap:10px; flex-shrink:0;">
          <span class="badge badge-info">${f.size_human}</span>
          ${previewBtn}
          <a class="btn btn-primary" style="padding:5px 10px; text-decoration:none;" href="${dlUrl}" download>Save File</a>
        </div>
      `;
      card.appendChild(row);
    }
  }

  CURRENT_OFFSET += data.items.length;
  document.getElementById("loadMoreBtn").style.display = data.has_more ? "inline-block" : "none";
}

function loadMoreFiles() {
  loadFiles(false);
}

function openLightbox(arcId, filePath, kind) {
  const url = fileUrl(arcId, filePath, 0);
  const dlUrl = fileUrl(arcId, filePath, 1);
  document.getElementById("modalTitle").textContent = "/" + filePath;
  document.getElementById("modalDownload").href = dlUrl;
  const body = document.getElementById("modalBody");
  if (kind === "image") {
    body.innerHTML = `<img src="${url}" style="max-width:86vw; max-height:76vh; border-radius:8px;">`;
  } else {
    body.innerHTML = `<video src="${url}" controls autoplay style="max-width:86vw; max-height:76vh; border-radius:8px;"></video>`;
  }
  document.getElementById("mediaModal").style.display = "flex";
}

function closeModal() {
  document.getElementById("modalBody").innerHTML = "";
  document.getElementById("mediaModal").style.display = "none";
}

// --- 5. Storage Cleanup & Management ("Danger Zone") ---
async function showManageView() {
  setActiveNav("navManage");
  hideAllViews();
  SELECTED_FOR_DELETE.clear();
  await refreshStatus();
  renderManageView();
  document.getElementById("manageView").style.display = "block";
}

function renderManageView() {
  const isWritable = !APP_STATE.readonly;
  document.getElementById("mgmtLockBox").style.display = isWritable ? "none" : "block";
  document.getElementById("mgmtActiveBox").style.display = isWritable ? "flex" : "none";

  document.getElementById("cacheSizeLbl").textContent = APP_STATE.cache_human || "0 B";
  const extCount = APP_STATE.extracted_count || 0;
  document.getElementById("extCountLbl").textContent = extCount;
  document.getElementById("btnCleanExtracted").style.display = extCount > 0 ? "inline-block" : "none";

  const archives = APP_STATE.archives || [];
  document.getElementById("mgmtTotalCount").textContent = archives.length;
  const list = document.getElementById("mgmtArchivesList");
  list.innerHTML = "";

  for (const a of archives) {
    const row = document.createElement("div");
    row.className = "file-row";
    const checked = SELECTED_FOR_DELETE.has(a.id) ? "checked" : "";
    const disabled = !isWritable ? "disabled" : "";
    row.innerHTML = `
      <label style="display:flex; align-items:center; gap:12px; flex:1; cursor:${isWritable ? 'pointer' : 'not-allowed'};">
        <input type="checkbox" ${checked} ${disabled} onchange="toggleMgmtSelect(${a.id}, this.checked)">
        <div>
          <div style="font-weight:700;">${a.type} ${a.vmid} — ${a.name} <span class="muted" style="font-weight:400;">(${a.date})</span></div>
          <div class="muted" style="font-size:0.82rem;">${a.filename} ${a.protected ? '• <strong style="color:#fde68a;">PROTECTED</strong>' : ''}</div>
        </div>
      </label>
      <span class="badge badge-info">${a.size_human}</span>
    `;
    list.appendChild(row);
  }
  updateMgmtSelectionUI();
}

function toggleMgmtSelect(id, checked) {
  if (checked) SELECTED_FOR_DELETE.add(id);
  else SELECTED_FOR_DELETE.delete(id);
  updateMgmtSelectionUI();
}

function selectOldBackups(days) {
  if (APP_STATE.readonly) return;
  const cutoff = Math.floor(Date.now() / 1000) - (days * 86400);
  const allowProt = document.getElementById("chkAllowProtected").checked;
  SELECTED_FOR_DELETE.clear();
  for (const a of APP_STATE.archives) {
    if (a.mtime < cutoff && (!a.protected || allowProt)) {
      SELECTED_FOR_DELETE.add(a.id);
    }
  }
  renderManageView();
}

function clearMgmtSelection() {
  SELECTED_FOR_DELETE.clear();
  renderManageView();
}

function updateMgmtSelectionUI() {
  const count = SELECTED_FOR_DELETE.size;
  document.getElementById("selCountLbl").textContent = count;
  document.getElementById("btnDeleteSelected").disabled = APP_STATE.readonly || count === 0;
}

async function enableManagementMode() {
  if (!document.getElementById("chkAcceptRisk").checked) {
    alert("Please check the confirmation box acknowledging that deletions are permanent and NOT MAWK's fault.");
    return;
  }
  const res = await api("/api/set_mode", {
    method: "POST",
    headers: {"Content-Type": "application/json"},
    body: JSON.stringify({readonly: false})
  });
  if (!res.ok) {
    alert(res.error || "Could not switch drive to read-write mode.");
    return;
  }
  await refreshStatus();
  renderManageView();
}

async function disableManagementMode() {
  const res = await api("/api/set_mode", {
    method: "POST",
    headers: {"Content-Type": "application/json"},
    body: JSON.stringify({readonly: true})
  });
  if (!res.ok) {
    alert(res.error || "Could not return to read-only mode.");
    return;
  }
  SELECTED_FOR_DELETE.clear();
  await refreshStatus();
  renderManageView();
}

async function deleteSelectedBackups() {
  const ids = Array.from(SELECTED_FOR_DELETE);
  if (ids.length === 0) return;
  const allowProt = document.getElementById("chkAllowProtected").checked;

  const confirmed = confirm(
    `FINAL WARNING — ARE YOU 100% SURE?\n\n` +
    `You are about to PERMANENTLY DELETE ${ids.length} backup archive(s) and their metadata from your drive.\n\n` +
    `This cannot be undone, and if you damage or lose data it is NOT MAWK's fault!\n\n` +
    `Click OK to permanently delete.`
  );
  if (!confirmed) return;

  const res = await api("/api/delete_backups", {
    method: "POST",
    headers: {"Content-Type": "application/json"},
    body: JSON.stringify({archive_ids: ids, delete_protected: allowProt})
  });
  if (!res.ok) {
    alert(res.error || "Delete failed.");
    return;
  }
  SELECTED_FOR_DELETE.clear();
  alert(`Deleted ${res.deleted_count} backup archive(s) and freed ${res.freed_human}.`);
  await refreshStatus();
  renderManageView();
}

async function cleanLocalData(target) {
  const msg = target === "extracted"
    ? "Delete all locally extracted backup folders from your computer's disk?"
    : "Clear temporary file indexes and media previews from your computer's temp folder?";
  if (!confirm(msg)) return;
  await api("/api/clean_local", {
    method: "POST",
    headers: {"Content-Type": "application/json"},
    body: JSON.stringify({target})
  });
  await refreshStatus();
  renderManageView();
}

async function shutdownApp() {
  let cleanExt = false;
  if (APP_STATE && APP_STATE.extracted_count > 0) {
    cleanExt = confirm("Delete locally extracted backup folder(s) from your PC before locking and exiting?\n\nOK = Delete extracted folders & exit\nCancel = Keep extracted folders & exit");
  }
  await api("/api/shutdown", {
    method: "POST",
    headers: {"Content-Type": "application/json"},
    body: JSON.stringify({cleanup_extracted: cleanExt})
  });
  document.body.innerHTML = `<div style="max-width:520px;margin:100px auto;background:#1e293b;padding:28px;border-radius:12px;text-align:center;">
    <h2 style="color:#22c55e;margin-top:0;">Drive Locked &amp; Session Closed</h2>
    <p style="color:#94a3b8;">All encryption keys have been unloaded and any imported ZFS pool has been safely exported. You may close this browser tab.</p>
  </div>`;
}

// Initial boot
(async function init() {
  await refreshStatus();
  await showSourcesView();
})();
</script>
</body>
</html>
"""


# --- HTTP Server with Range Support for Video Scrubbing ---
class ThreadingHTTPServer(socketserver.ThreadingMixIn, http.server.HTTPServer):
    daemon_threads = True


class BackupExplorerHandler(http.server.BaseHTTPRequestHandler):
    def log_message(self, format, *args):
        pass

    def _check_auth(self, parsed):
        qs = urllib.parse.parse_qs(parsed.query)
        tok = qs.get("token", [""])[0]
        return secrets.compare_digest(tok, SESSION_TOKEN)

    def _send_json(self, payload, status=200):
        raw = json.dumps(payload).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(raw)))
        self.end_headers()
        self.wfile.write(raw)

    def _read_json_body(self):
        length = int(self.headers.get("Content-Length", "0"))
        if length <= 0:
            return {}
        return json.loads(self.rfile.read(length).decode("utf-8"))

    def do_GET(self):
        parsed = urllib.parse.urlparse(self.path)
        if not self._check_auth(parsed):
            self.send_error(403, "Invalid session token")
            return

        if parsed.path == "/":
            raw = HTML_PAGE.encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(raw)))
            self.end_headers()
            self.wfile.write(raw)
            return

        if parsed.path == "/api/sources":
            qs = urllib.parse.parse_qs(parsed.query)
            inc_sys = qs.get("include_system", ["0"])[0] == "1"
            self._send_json(discover_sources(include_system=inc_sys))
            return

        if parsed.path == "/api/status":
            default_dir = os.path.join(DESKTOP_HOME, "Downloads") if os.path.isdir(os.path.join(DESKTOP_HOME, "Downloads")) else DESKTOP_HOME
            cache_bytes = folder_size_bytes(CACHE_DIR) + folder_size_bytes(PREVIEW_DIR)
            self._send_json({
                "source": ACTIVE_SOURCE,
                "locked": POOL_LOCKED,
                "readonly": READONLY_MODE,
                "archives": ARCHIVES,
                "task": TASK_STATUS,
                "extracted_count": len(EXTRACTED_DIRS),
                "cache_human": human_size(cache_bytes),
                "default_extract_dir": default_dir,
            })
            return

        if parsed.path == "/api/files":
            qs = urllib.parse.parse_qs(parsed.query)
            arc_id = int(qs.get("archive_id", ["0"])[0])
            tab = qs.get("tab", ["media"])[0]
            q = qs.get("q", [""])[0].strip().lower()
            offset = int(qs.get("offset", ["0"])[0])
            limit = min(int(qs.get("limit", ["90"])[0]), 250)

            all_entries = INDEX_CACHE.get(arc_id, [])
            if tab == "media":
                filtered = [e for e in all_entries if e["kind"] in ("image", "video")]
            elif tab == "docs":
                filtered = [e for e in all_entries if e["kind"] == "doc"]
            elif tab == "largest":
                filtered = sorted(all_entries, key=lambda x: x["size"], reverse=True)[:200]
            else:
                filtered = all_entries

            if q:
                filtered = [e for e in filtered if q in e["path"].lower()]

            page = filtered[offset : offset + limit]
            self._send_json({
                "items": page,
                "total": len(filtered),
                "has_more": (offset + len(page)) < len(filtered),
            })
            return

        if parsed.path == "/api/stream":
            qs = urllib.parse.parse_qs(parsed.query)
            arc_id = int(qs.get("archive_id", ["0"])[0])
            rel_path = qs.get("path", [""])[0]
            download = qs.get("download", ["0"])[0] == "1"

            local_file = resolve_single_file_on_disk(arc_id, rel_path)
            if not local_file or not os.path.isfile(local_file):
                self.send_error(404, "File not found in backup")
                return

            file_size = os.path.getsize(local_file)
            ctype, _ = mimetypes.guess_type(local_file)
            ctype = ctype or "application/octet-stream"

            range_hdr = self.headers.get("Range")
            start, end = 0, file_size - 1
            status_code = 200

            if range_hdr and range_hdr.startswith("bytes="):
                m = re.match(r"bytes=(\d*)-(\d*)", range_hdr)
                if m:
                    if m.group(1):
                        start = int(m.group(1))
                    if m.group(2):
                        end = min(int(m.group(2)), file_size - 1)
                    status_code = 206

            chunk_len = max(0, end - start + 1)
            self.send_response(status_code)
            self.send_header("Content-Type", ctype)
            self.send_header("Accept-Ranges", "bytes")
            self.send_header("Content-Length", str(chunk_len))
            if status_code == 206:
                self.send_header("Content-Range", f"bytes {start}-{end}/{file_size}")
            if download:
                fn = os.path.basename(local_file).replace('"', "")
                self.send_header("Content-Disposition", f'attachment; filename="{fn}"')
            self.end_headers()

            with open(local_file, "rb") as f:
                f.seek(start)
                remaining = chunk_len
                while remaining > 0:
                    buf = f.read(min(262144, remaining))
                    if not buf:
                        break
                    self.wfile.write(buf)
                    remaining -= len(buf)
            return

        self.send_error(404)

    def do_POST(self):
        global POOL_LOCKED, TASK_STATUS, ARCHIVES
        parsed = urllib.parse.urlparse(self.path)
        if not self._check_auth(parsed):
            self.send_error(403, "Invalid session token")
            return

        body = self._read_json_body()

        if parsed.path == "/api/select_source":
            kind = body.get("kind", "")
            target = body.get("target", "").strip()
            ro = bool(body.get("readonly", True))
            try:
                activate_source(kind, target, readonly=ro)
                TASK_STATUS.update({"running": False, "message": "Idle — Ready", "error": ""})
                self._send_json({"ok": True})
            except Exception as exc:
                TASK_STATUS.update({"running": False, "message": "Idle — Ready", "error": ""})
                self._send_json({"ok": False, "error": str(exc)})
            return

        if parsed.path == "/api/unlock":
            pw = body.get("passphrase", "")
            zfs_cmd = "zfs.exe" if IS_WINDOWS else "zfs"
            pool = ACTIVE_SOURCE["target"]
            res = run_cmd([zfs_cmd, "load-key", pool], input_text=pw + "\n")
            if res.returncode != 0:
                self._send_json({"ok": False, "error": "Incorrect passphrase."})
                return
            try:
                mount_and_index_active_source()
                POOL_LOCKED = False
                self._send_json({"ok": True})
            except Exception as exc:
                self._send_json({"ok": False, "error": str(exc)})
            return

        if parsed.path == "/api/set_mode":
            new_ro = bool(body.get("readonly", True))
            try:
                switch_pool_readonly_state(new_ro)
                self._send_json({"ok": True})
            except Exception as exc:
                self._send_json({"ok": False, "error": str(exc)})
            return

        if parsed.path == "/api/open_snapshot":
            arc_id = int(body.get("archive_id", 0))
            TASK_STATUS = {"running": True, "kind": "index", "message": "Scanning backup table of contents...", "percent": 5, "error": ""}
            threading.Thread(target=index_archive_worker, args=(arc_id,), daemon=True).start()
            self._send_json({"ok": True})
            return

        if parsed.path == "/api/extract_full":
            arc_id = int(body.get("archive_id", 0))
            dest_dir = body.get("dest_dir", "").strip()
            if not dest_dir:
                self._send_json({"ok": False, "error": "Destination folder is required."})
                return
            TASK_STATUS = {"running": True, "kind": "extract", "message": f"Extracting to {dest_dir}...", "percent": 10, "error": ""}
            threading.Thread(target=extract_full_worker, args=(arc_id, dest_dir), daemon=True).start()
            self._send_json({"ok": True})
            return

        if parsed.path == "/api/cancel_task":
            CANCEL_EVENT.set()
            remove_partial_extraction()
            TASK_STATUS.update({"running": False, "message": "Cancelled by user", "percent": 0})
            self._send_json({"ok": True})
            return

        if parsed.path == "/api/delete_backups":
            if READONLY_MODE:
                self._send_json({"ok": False, "error": "Management Mode (Read-Write) must be unlocked first."})
                return
            arc_ids = set(int(x) for x in body.get("archive_ids", []))
            del_prot = bool(body.get("delete_protected", False))
            deleted_count = 0
            freed_bytes = 0
            real_dump = os.path.realpath(DUMP_DIR)

            for arc in list(ARCHIVES):
                if arc["id"] not in arc_ids:
                    continue
                if arc["protected"] and not del_prot:
                    continue
                arc_real = os.path.realpath(arc["path"])
                if not arc_real.startswith(real_dump + os.sep):
                    continue

                prefix = re.sub(r"\.(tar|vma)(\.(zst|gz|lzo|bz2|xz))?$", "", arc_real)
                sidecars = [arc_real, arc_real + ".notes", prefix + ".log"]
                if del_prot:
                    sidecars.append(arc_real + ".protected")

                for fp in sidecars:
                    if os.path.isfile(fp):
                        try:
                            freed_bytes += os.path.getsize(fp)
                            os.remove(fp)
                        except OSError:
                            pass
                deleted_count += 1

            ARCHIVES = scan_dump_archives(DUMP_DIR)
            INDEX_CACHE.clear()
            self._send_json({"ok": True, "deleted_count": deleted_count, "freed_human": human_size(freed_bytes)})
            return

        if parsed.path == "/api/clean_local":
            target = body.get("target", "")
            if target == "cache":
                shutil.rmtree(CACHE_DIR, ignore_errors=True)
                shutil.rmtree(PREVIEW_DIR, ignore_errors=True)
                INDEX_CACHE.clear()
            elif target == "extracted":
                for p in list(EXTRACTED_DIRS.values()):
                    if p and os.path.isdir(p):
                        shutil.rmtree(p, ignore_errors=True)
                EXTRACTED_DIRS.clear()
            self._send_json({"ok": True})
            return

        if parsed.path == "/api/eject_source":
            release_active_source(export_pool=True)
            self._send_json({"ok": True})
            return

        if parsed.path == "/api/shutdown":
            clean_ext = bool(body.get("cleanup_extracted", False))
            self._send_json({"ok": True})
            threading.Thread(target=lambda: (time.sleep(0.3), cleanup_and_exit(cleanup_extracted=clean_ext), os._exit(0)), daemon=True).start()
            return

        self.send_error(404)


def main():
    global SERVER_INSTANCE
    ensure_privileges()

    SERVER_INSTANCE = ThreadingHTTPServer(("127.0.0.1", 0), BackupExplorerHandler)
    port = SERVER_INSTANCE.server_address[1]
    url = f"http://127.0.0.1:{port}/?token={SESSION_TOKEN}"

    print(f"[+] Proxmox Backup Explorer v{APP_VERSION} running on {url}")
    print("[*] Press Ctrl+C at any time to cancel active operations, clean partial files, lock ZFS, and exit.")
    open_browser_as_user(url)

    try:
        SERVER_INSTANCE.serve_forever()
    except KeyboardInterrupt:
        handle_sigint(signal.SIGINT, None)


if __name__ == "__main__":
    main()

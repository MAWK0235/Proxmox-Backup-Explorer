# Proxmox Backup Explorer

A cross-platform, single-file utility for **Linux** and **Windows** that safely mounts, decrypts, and explores Proxmox VE (`vzdump`) container and VM backups stored on **encrypted or unencrypted ZFS external drives**, network shares, or local folders.

## Features

- **Universal Drive & Folder Discovery:**
  - Automatically detects any external ZFS pool (`zpool import`), pre-mounted ZFS datasets, or local/network backup folders (`dump/`).
  - Supports both **ZFS native encryption** (passphrase prompt) and **unencrypted ZFS pools**.
- **Safe Read-Only Default & Clean Ejection:**
  - Imports ZFS pools with `-o readonly=on -o cachefile=none` so workstation mounts never alter pool feature flags or register auto-mount caches.
  - Unloads encryption keys (`zfs unload-key`) and exports the pool (`zpool export`) on exit or `Ctrl+C`.
- **Smart Content Views (No Linux Path Knowledge Required):**
  - **Photos & Videos Gallery:** Inline image thumbnails, lightbox viewer, and HTML5 video player with scrubbing (ideal for Immich, Nextcloud, or media containers).
  - **Largest Files Finder:** Instantly ranks the top 200 largest files in any container backup.
  - **Documents & Configs / Instant Search:** Search across every file inside a `.tar.zst` backup and download individual files without unpacking the entire archive.
- **Persistent Action & Live Status Sidebar:**
  - Real-time progress bar with an instant **Cancel Ongoing Action** button that kills active scans/extractions and deletes incomplete files.
- **Storage Cleanup & Management ("Danger Zone"):**
  - Opt-in read-write management mode to prune old snapshots or clear local preview/extraction caches.

## Prerequisites

- **Linux:** `zfsutils-linux` (`sudo apt install zfsutils-linux`) and Python 3.9+
- **Windows:** [OpenZFS on Windows](https://github.com/openzfsonwindows/openzfs/releases) and Python 3.9+
- *(Optional)* `pip install zstandard` for faster in-memory `.tar.zst` indexing (falls back automatically to system `zstd` or `tar`).

## Quick Start

### Run Directly from Source
```bash
# Linux
sudo python3 proxmox_backup_explorer.py

# Windows (Run PowerShell as Administrator)
python proxmox_backup_explorer.py

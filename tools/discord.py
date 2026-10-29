#!/usr/bin/env python3
"""조이봉방 스레드 읽기·답장 도구 (Claude 작업자용).

사용:
  python tools/discord.py read [--limit 30]     최근 메시지를 오래된 순으로 출력
  python tools/discord.py reply <md파일> --to <message_id>   해당 메시지에 답장
봇 토큰은 ~/.all-tomorrow/key-pool.env 의 EVE_DISCORD_BOT_TOKEN에서 읽고 출력하지 않는다.
"""

import argparse
import json
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")

THREAD_ID = (Path(__file__).resolve().parent / "thread_id.txt").read_text(encoding="utf-8").strip()
API = "https://discord.com/api/v10"
MAX_CHUNK = 1900


def token() -> str:
    for line in (Path.home() / ".all-tomorrow" / "key-pool.env").read_text(encoding="utf-8").splitlines():
        key, _, value = line.partition("=")
        if key.strip() == "EVE_DISCORD_BOT_TOKEN" and value.strip():
            return value.strip().strip("'\"")
    raise SystemExit("봇 토큰 없음")


def call(method: str, path: str, body: dict | None = None):
    req = urllib.request.Request(API + path, method=method,
                                 data=json.dumps(body).encode() if body is not None else None,
                                 headers={"Authorization": f"Bot {token()}", "Content-Type": "application/json",
                                          "User-Agent": "DiscordBot (joibongbang, 1)"})
    for attempt in range(3):
        try:
            with urllib.request.urlopen(req, timeout=20) as r:
                return json.load(r)
        except urllib.error.HTTPError as e:
            if e.code == 429 and attempt < 2:
                time.sleep(float(json.loads(e.read() or b"{}").get("retry_after", 2)))
                continue
            raise SystemExit(f"Discord HTTP {e.code}")


def read(limit: int) -> None:
    for m in reversed(call("GET", f"/channels/{THREAD_ID}/messages?limit={min(limit, 100)}")):
        who = m["author"].get("global_name") or m["author"]["username"]
        bot = " (봇)" if m["author"].get("bot") else ""
        print(f"[{m['id']}] {m['timestamp'][:16]} {who}{bot}: {m.get('content', '')}")
        for a in m.get("attachments", []):
            print(f"    첨부: {a.get('filename')} {a.get('url')}")


def reply(md: Path, to: str) -> None:
    text = md.read_text(encoding="utf-8").strip()
    chunks, cur = [], ""
    for line in text.splitlines(keepends=True):
        if len(cur) + len(line) > MAX_CHUNK:
            chunks.append(cur)
            cur = ""
        cur += line
    chunks.append(cur)
    for i, chunk in enumerate(c for c in chunks if c.strip()):
        body = {"content": chunk, "allowed_mentions": {"parse": []}}
        if i == 0:
            body["message_reference"] = {"message_id": to, "fail_if_not_exists": False}
        call("POST", f"/channels/{THREAD_ID}/messages", body)
    print("답장 완료")


p = argparse.ArgumentParser()
sub = p.add_subparsers(dest="cmd", required=True)
r = sub.add_parser("read"); r.add_argument("--limit", type=int, default=30)
w = sub.add_parser("reply"); w.add_argument("file", type=Path); w.add_argument("--to", required=True)
a = p.parse_args()
read(a.limit) if a.cmd == "read" else reply(a.file, a.to)

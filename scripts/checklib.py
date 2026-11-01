"""Helpers that the check scripts share: free ports, checks, waiting, and replies in the API's format.

`clerk_check.py`, `seat_check.py` and `deploy_check.py` import this file. Each script keeps its own
stand-in for the API, because each needs different replies, but they all answer in the same format.
"""
import json, socket, time


def free_port():
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


def check(ok, what):
    if not ok:
        raise SystemExit(f"FAILED: {what}")
    print(f"ok: {what}")


def wait_for(test, what, seconds=30):
    end = time.time() + seconds
    while time.time() < end:
        v = test()
        if v:
            return v
        time.sleep(0.02)
    raise SystemExit(f"FAILED: timed out waiting for {what}")


def send_events(handler, events):
    """Send these events as a stream. A client that has gone away is not a problem here."""
    handler.send_response(200)
    handler.send_header("content-type", "text/event-stream")
    handler.end_headers()
    try:
        for e in events:
            handler.wfile.write(f"event: {e['type']}\ndata: {json.dumps(e)}\n\n".encode())
            handler.wfile.flush()
    except OSError:
        pass


def send_text(handler, text, usage, stop="end_turn", output_tokens=3):
    """A whole reply of one text block, as the API streams it. `usage` is the input side of the token count."""
    send_events(handler, [
        {"type": "message_start", "message": {"usage": usage}},
        {"type": "content_block_start", "content_block": {"type": "text"}},
        {"type": "content_block_delta", "delta": {"type": "text_delta", "text": text}},
        {"type": "message_delta", "delta": {"stop_reason": stop}, "usage": {"output_tokens": output_tokens}},
        {"type": "message_stop"},
    ])


def send_error(handler, status, kind, message, retry=None, raw=None):
    """An error reply, in the API's JSON format unless `raw` gives the body. `retry` sets retry-after."""
    payload = raw.encode() if raw is not None else json.dumps({"type": "error", "error": {"type": kind, "message": message}}).encode()
    handler.send_response(status)
    handler.send_header("content-type", "application/json")
    if retry is not None:
        handler.send_header("retry-after", str(retry))
    handler.send_header("content-length", str(len(payload)))
    handler.end_headers()
    handler.wfile.write(payload)

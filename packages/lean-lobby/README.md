# lean-lobby

A pure, kernel-checked room state machine for multiplayer games: create a room by code, join with a caller-minted token, leave, reconnect to the same seat, and start once enough seats are filled.

Lean 4 (`leanprover/lean4:v4.35.0`). No dependencies (no Mathlib, no Batteries). Library `Lobby`.

## Non-goals

- No IO, networking, timers, or persistence. The caller drives `Lobby.step` and stores the result.
- No randomness. The caller mints room codes and player tokens (for example from random bits).
- No authentication beyond tokens. `start` takes no token: the caller decides who may start (for example the host).
- No spectators, kicking, seat swapping, or host transfer in v0.1.
- Tokens are unique *per room*. The same token may sit in two different rooms (one player in two games).

## Guarantees

All theorems are in `Lobby/Theorems.lean`. `Reachable l` means `l` is obtained from `Lobby.empty` by
any sequence of `Lobby.step` calls.

```lean
-- No two filled seats of a room share a token.
theorem Lobby.seat_unique {l : Lobby} (hl : Reachable l) {r : Room} (hr : r ∈ l.rooms) :
    r.tokens.Nodup

-- A token holds at most one seat: two seats with the same token are the same seat.
theorem Lobby.seat_unique_index {l : Lobby} (hl : Reachable l) {r : Room} (hr : r ∈ l.rooms)
    {i j : Nat} {a b : SeatInfo} (ha : r.seats[i]? = some (some a))
    (hb : r.seats[j]? = some (some b)) (hab : a.token = b.token) : i = j

-- Reconnecting with a seated token gives back the same seat (same index, name, token),
-- now connected; no other seat changes and the started flag is kept.
theorem Lobby.reconnect_restores {l : Lobby} {c t : String} {r : Room} {i : Nat} {s : SeatInfo}
    (h : l.room? c = some r) (hs : r.seatOf? t = some (i, s)) :
    (l.step (.reconnect c t)).2 = [.reconnected c i s.name] ∧
    ∃ r', (l.step (.reconnect c t)).1.room? c = some r' ∧
      r'.seatOf? t = some (i, { s with connected := true }) ∧
      r'.started = r.started ∧
      ∀ j, j ≠ i → r'.seats[j]? = r.seats[j]?

-- In a started room, leave then reconnect with the same token restores the room exactly
-- (if the seat was connected before).
theorem Lobby.leave_reconnect_restores {l : Lobby} {c t : String} {r : Room} {i : Nat}
    {s : SeatInfo} (h : l.room? c = some r) (hst : r.started = true)
    (hs : r.seatOf? t = some (i, s)) (hcon : s.connected = true) :
    ((l.step (.leave c t)).1.step (.reconnect c t)).1.room? c = some r

-- `start` on a room that has not started succeeds iff at least `minSeats` seats are filled.
theorem Lobby.start_iff_min {l : Lobby} {c : String} {r : Room} (h : l.room? c = some r)
    (hns : r.started = false) :
    ((l.step (.start c)).1.room? c).map (·.started) = some true ↔ r.minSeats ≤ r.filled

-- A started room always has at least `minSeats` filled seats (leaving after start keeps the seat).
theorem Lobby.started_has_min {l : Lobby} (hl : Reachable l) {r : Room} (hr : r ∈ l.rooms)
    (hs : r.started = true) : r.minSeats ≤ r.filled

-- Joining a full room is rejected and changes nothing.
theorem Lobby.join_full_rejected {l : Lobby} {c : String} {r : Room} (h : l.room? c = some r)
    (hf : r.isFull = true) (name token : String) :
    l.step (.join c name token) = (l, [.rejected c .roomFull])

-- The full room invariant (size = maxSeats, 0 < min ≤ max, distinct tokens, started ⇒ min).
theorem Lobby.reachable_wf {l : Lobby} (hl : Reachable l) : ∀ r ∈ l.rooms, r.WF

-- `isFull` means no seat is empty.
theorem Lobby.Room.isFull_iff {r : Room} : r.isFull = true ↔ ∀ x ∈ r.seats.toList, x.isSome
```

Axiom audit (`lake build` prints it from `Lobby/Audit.lean`):

```
'Lobby.seat_unique' depends on axioms: [propext, Quot.sound]
'Lobby.seat_unique_index' depends on axioms: [propext, Quot.sound]
'Lobby.reconnect_restores' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lobby.leave_reconnect_restores' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lobby.start_iff_min' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lobby.started_has_min' depends on axioms: [propext, Quot.sound]
'Lobby.join_full_rejected' depends on axioms: [propext]
'Lobby.reachable_wf' depends on axioms: [propext, Quot.sound]
'Lobby.Room.isFull_iff' depends on axioms: [propext, Quot.sound]
```

No `sorry`, `admit`, `native_decide`, or new axioms.

## What is tested but not proved

- Exact notice sequences for concrete scenarios (create, duplicate code, bad seat range, join order,
  `tokenInUse`, leave before start frees the lowest seat, `notEnoughPlayers`, `alreadyStarted`,
  disconnect and reconnect after start, `unknownToken`, full room): `#guard` checks in
  `LobbyTests/Basic.lean`, run by `lake build`.
- Room codes stay unique across a lobby (create rejects duplicates; this is not stated as a theorem).
- Every command yields exactly one notice, and the room invariant holds on 300 random runs of 60
  commands each: `lake test` (`LobbyTests/Main.lean`).

## Quickstart

```toml
# lakefile.toml
[[require]]
name = "lobby"
path = "../lean-lobby"
```

```lean
import Lobby
open Lobby

def demo : Lobby × List Notice :=
  Lobby.empty.run [
    .create "ABCD" 2 4,               -- 2..4 seats
    .join "ABCD" "ann" "tok-ann",     -- tokens come from your RNG
    .join "ABCD" "bob" "tok-bob",
    .start "ABCD",
    .leave "ABCD" "tok-bob",          -- after start: seat kept, marked disconnected
    .reconnect "ABCD" "tok-bob"]      -- same seat back
-- demo.2 = [.created "ABCD", .joined "ABCD" 0 "ann", .joined "ABCD" 1 "bob",
--           .started "ABCD" 2, .disconnected "ABCD" 1, .reconnected "ABCD" 1 "bob"]
```

Semantics in brief:

| Command | Effect | Rejections |
|---|---|---|
| `create code min max` | new room, `max` empty seats | `duplicateCode`, `badSeatRange` (needs `0 < min ≤ max`) |
| `join code name token` | lowest empty seat | `noSuchRoom`, `roomFull`, `alreadyStarted`, `tokenInUse` |
| `reconnect code token` | the token's seat becomes connected | `noSuchRoom`, `unknownToken` |
| `leave code token` | before start: seat freed; after start: seat kept, disconnected | `noSuchRoom`, `unknownToken` |
| `start code` | `started := true` | `noSuchRoom`, `alreadyStarted`, `notEnoughPlayers` |

A rejected command returns the lobby unchanged and one `Notice.rejected code reason`.

Build and test: `lake build` (library, `#guard` tests, axiom audit), `lake test` (random driver).

## Second use case: a chess room

`examples/ChessRoom.lean` runs a two-seat chess table (White = seat 0, Black = seat 1). A third
player is turned away, the clock starts, Black's connection drops and Black reconnects to the
same seat. Run it with `lake exe chess_room`:

```
[K7Q2] chess table opened
[K7Q2] Magnus sits down with White
[K7Q2] Hikaru sits down with Black
[K7Q2] rejected: Lobby.Reject.roomFull
[K7Q2] clock started
[K7Q2] seat 1 lost connection; clock keeps running
[K7Q2] Hikaru is back on seat 1
```

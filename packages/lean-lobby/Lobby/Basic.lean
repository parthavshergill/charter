/-!
# Lobby: a pure room state machine

A `Lobby` holds rooms. Each room has a code, a seat range `minSeats..maxSeats`,
an array of `maxSeats` seats (empty or filled), and a `started` flag.

Players are identified by an opaque *token* that the caller generates (for example
from random bits) and hands to the player on `join`. The token is the only
credential: `reconnect` and `leave` name the seat by token.

All operations are total and pure. A rejected command leaves the lobby unchanged
and produces exactly one `Notice.rejected`.
-/

namespace Lobby

/-- A filled seat. -/
structure SeatInfo where
  name : String
  token : String
  connected : Bool := true
deriving Repr, DecidableEq, Inhabited

/-- One room. `seats.size = maxSeats` is an invariant (see `Room.WF`). -/
structure Room where
  code : String
  minSeats : Nat
  maxSeats : Nat
  seats : Array (Option SeatInfo)
  started : Bool
deriving Repr, DecidableEq, Inhabited

/-- Commands from clients (the caller authenticates `start` itself). -/
inductive Cmd where
  | create (code : String) (min max : Nat)
  | join (code name : String) (token : String)
  | reconnect (code token : String)
  | leave (code token : String)
  | start (code : String)
deriving Repr, DecidableEq, Inhabited

/-- Why a command was rejected. -/
inductive Reject where
  | duplicateCode
  | badSeatRange (min max : Nat)
  | noSuchRoom
  | roomFull
  | alreadyStarted
  | tokenInUse
  | unknownToken
  | notEnoughPlayers (filled min : Nat)
deriving Repr, DecidableEq, Inhabited

/-- What happened, for broadcasting to clients. -/
inductive Notice where
  | created (code : String)
  | joined (code : String) (seat : Nat) (name : String)
  | reconnected (code : String) (seat : Nat) (name : String)
  /-- Seat freed (room not started yet). -/
  | left (code : String) (seat : Nat)
  /-- Seat kept but marked disconnected (room already started). -/
  | disconnected (code : String) (seat : Nat)
  | started (code : String) (filled : Nat)
  | rejected (code : String) (why : Reject)
deriving Repr, DecidableEq, Inhabited

/-! ## Seat-list helpers (on `List`, for easy reasoning) -/

/-- The first seat held by token `t`, with its index. -/
def findSeat (t : String) : List (Option SeatInfo) → Option (Nat × SeatInfo)
  | [] => none
  | some s :: rest =>
    if s.token = t then some (0, s) else (findSeat t rest).map fun p => (p.1 + 1, p.2)
  | none :: rest => (findSeat t rest).map fun p => (p.1 + 1, p.2)

/-- The index of the first empty seat. -/
def firstEmpty : List (Option SeatInfo) → Option Nat
  | [] => none
  | none :: _ => some 0
  | some _ :: rest => (firstEmpty rest).map (· + 1)

namespace Room

/-- A fresh room with `max` empty seats. -/
def new (code : String) (min max : Nat) : Room :=
  { code, minSeats := min, maxSeats := max, seats := Array.replicate max none, started := false }

/-- The filled seats, in seat order. -/
def occupants (r : Room) : List SeatInfo := r.seats.toList.filterMap id

/-- Tokens of all filled seats, in seat order. -/
def tokens (r : Room) : List String := r.occupants.map (·.token)

/-- Number of filled seats. -/
def filled (r : Room) : Nat := r.occupants.length

/-- No seat is empty. -/
def isFull (r : Room) : Bool := (firstEmpty r.seats.toList).isNone

/-- The seat held by token `t`. -/
def seatOf? (r : Room) (t : String) : Option (Nat × SeatInfo) := findSeat t r.seats.toList

/-- Replace seat `i`. -/
def setSeat (r : Room) (i : Nat) (s : Option SeatInfo) : Room :=
  { r with seats := r.seats.setIfInBounds i s }

/-- Join: rejected if full, started, or the token already holds a seat. -/
def join (r : Room) (name token : String) : Except Reject (Room × Notice) :=
  if r.isFull then .error .roomFull
  else if r.started then .error .alreadyStarted
  else match r.seatOf? token with
    | some _ => .error .tokenInUse
    | none =>
      match firstEmpty r.seats.toList with
      | none => .error .roomFull
      | some i => .ok (r.setSeat i (some { name, token, connected := true }),
                       .joined r.code i name)

/-- Reconnect: the token's seat becomes connected again; nothing else changes. -/
def reconnect (r : Room) (token : String) : Except Reject (Room × Notice) :=
  match r.seatOf? token with
  | none => .error .unknownToken
  | some (i, s) => .ok (r.setSeat i (some { s with connected := true }),
                        .reconnected r.code i s.name)

/-- Leave: before start the seat is freed; after start it is kept and marked
disconnected, so the player can `reconnect`. -/
def leave (r : Room) (token : String) : Except Reject (Room × Notice) :=
  match r.seatOf? token with
  | none => .error .unknownToken
  | some (i, s) =>
    if r.started then .ok (r.setSeat i (some { s with connected := false }), .disconnected r.code i)
    else .ok (r.setSeat i none, .left r.code i)

/-- Start: only if not started and at least `minSeats` seats are filled. -/
def start (r : Room) : Except Reject (Room × Notice) :=
  if r.started then .error .alreadyStarted
  else if r.filled < r.minSeats then .error (.notEnoughPlayers r.filled r.minSeats)
  else .ok ({ r with started := true }, .started r.code r.filled)

/-- The room invariant maintained by `Lobby.step`. -/
structure WF (r : Room) : Prop where
  size_eq : r.seats.size = r.maxSeats
  min_pos : 0 < r.minSeats
  min_le_max : r.minSeats ≤ r.maxSeats
  tokens_nodup : r.tokens.Nodup
  started_min : r.started = true → r.minSeats ≤ r.filled

end Room
end Lobby

/-- A set of rooms, keyed by code. -/
structure Lobby where
  rooms : List Lobby.Room := []
deriving Repr, DecidableEq, Inhabited

namespace Lobby

open Lobby (Room Cmd Notice Reject)

def empty : Lobby := ⟨[]⟩

/-- The room with code `c` (first match; codes are unique by construction). -/
def room? (l : Lobby) (c : String) : Option Room := l.rooms.find? (·.code == c)

/-- Replace every room with code `c` by `r`. -/
def put (l : Lobby) (c : String) (r : Room) : Lobby :=
  ⟨l.rooms.map fun r' => if r'.code = c then r else r'⟩

/-- Run a room operation on room `c`. Errors leave the lobby unchanged. -/
def onRoom (l : Lobby) (c : String) (f : Room → Except Reject (Room × Notice)) :
    Lobby × List Notice :=
  match l.room? c with
  | none => (l, [.rejected c .noSuchRoom])
  | some r =>
    match f r with
    | .error e => (l, [.rejected c e])
    | .ok (r', n) => (l.put c r', [n])

/-- The lobby transition function. -/
def step (l : Lobby) : Cmd → Lobby × List Notice
  | .create c min max =>
    if (l.room? c).isSome then (l, [.rejected c .duplicateCode])
    else if min = 0 ∨ max < min then (l, [.rejected c (.badSeatRange min max)])
    else (⟨l.rooms ++ [Room.new c min max]⟩, [.created c])
  | .join c name token => l.onRoom c (·.join name token)
  | .reconnect c token => l.onRoom c (·.reconnect token)
  | .leave c token => l.onRoom c (·.leave token)
  | .start c => l.onRoom c Room.start

/-- Run many commands, collecting notices. -/
def run (l : Lobby) (cs : List Cmd) : Lobby × List Notice :=
  cs.foldl (fun (acc : Lobby × List Notice) c =>
    let (l', ns) := acc.1.step c
    (l', acc.2 ++ ns)) (l, [])

/-- Lobbies reachable from `empty` by `step`. -/
inductive Reachable : Lobby → Prop where
  | empty : Reachable Lobby.empty
  | step {l : Lobby} (c : Cmd) : Reachable l → Reachable (l.step c).1

end Lobby

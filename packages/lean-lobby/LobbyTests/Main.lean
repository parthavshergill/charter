import LobbyTests.Basic
import Lobby

/-! Randomized invariant test: run random command sequences and check the room invariant
(distinct tokens, size, started ⇒ min) on every intermediate lobby. The invariant is also
proved (`Lobby.reachable_wf`); this driver exercises the executable code path. -/

open Lobby

def checkRoom (r : Room) : Bool :=
  r.seats.size == r.maxSeats && 0 < r.minSeats && r.minSeats ≤ r.maxSeats &&
  (r.tokens.eraseDups.length == r.tokens.length) &&
  (!r.started || r.minSeats ≤ r.filled)

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

def pick (s : UInt64) (n : Nat) : Nat := ((s >>> 33).toNat) % n

def randCmd (s : UInt64) : Cmd :=
  let codes := #["A", "B", "C"]
  let toks := #["t0", "t1", "t2", "t3", "t4"]
  let c := codes[pick s 3]!
  let t := toks[pick (lcg s) 5]!
  match pick (lcg (lcg s)) 6 with
  | 0 => .create c (pick s 3) (pick (lcg s) 5)
  | 1 | 2 => .join c ("p" ++ t) t
  | 3 => .reconnect c t
  | 4 => .leave c t
  | _ => .start c

def main : IO UInt32 := do
  let mut failures := 0
  let mut seed : UInt64 := 42
  let mut notices := 0
  for _run in [0:300] do
    let mut l := Lobby.empty
    for _ in [0:60] do
      seed := lcg seed
      let (l', ns) := l.step (randCmd seed)
      notices := notices + ns.length
      if ns.length != 1 then failures := failures + 1
      l := l'
      unless l.rooms.all checkRoom do failures := failures + 1
      -- codes unique
      unless (l.rooms.map (·.code)).eraseDups.length == l.rooms.length do failures := failures + 1
  IO.println s!"lobby_tests: 300 runs x 60 commands, {notices} notices, {failures} failures"
  return if failures == 0 then 0 else 1

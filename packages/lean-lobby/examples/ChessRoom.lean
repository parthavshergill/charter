import Lobby

/-! Second use case: a two-player chess room. White and black are seats 0 and 1.
A chess server keeps one `Lobby`, mints tokens from its own RNG, and broadcasts notices. -/

open Lobby

def chessRoom (code : String) : Cmd := .create code 2 2

def describe : Notice → String
  | .created c => s!"[{c}] chess table opened"
  | .joined c 0 n => s!"[{c}] {n} sits down with White"
  | .joined c _ n => s!"[{c}] {n} sits down with Black"
  | .started c _ => s!"[{c}] clock started"
  | .disconnected c i => s!"[{c}] seat {i} lost connection; clock keeps running"
  | .reconnected c i n => s!"[{c}] {n} is back on seat {i}"
  | .left c i => s!"[{c}] seat {i} stood up"
  | .rejected c why => s!"[{c}] rejected: {repr why}"

def main : IO Unit := do
  let script : List Cmd := [
    chessRoom "K7Q2",
    .join "K7Q2" "Magnus" "tok-m",
    .join "K7Q2" "Hikaru" "tok-h",
    .join "K7Q2" "Kibitzer" "tok-k",   -- table is full
    .start "K7Q2",
    .leave "K7Q2" "tok-h",            -- wifi drops
    .reconnect "K7Q2" "tok-h"         -- same seat, still Black
  ]
  let (_, notices) := Lobby.empty.run script
  for n in notices do IO.println (describe n)

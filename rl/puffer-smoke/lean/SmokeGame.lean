/-! A tiny four-seat game for a linking smoke test. It is not the Charter engine.

Twelve cells hold values. Seats take turns and claim one cell. After eight
claims the game ends, so four cells stay unclaimed and the seats' total varies. -/

namespace Smoke

structure State where
  cells  : Array UInt32
  scores : Array UInt32
  seat   : UInt32
  ply    : UInt32
  rng    : UInt32

def numCells : Nat := 12
def numSeats : UInt32 := 4
def numPlies : UInt32 := 8

@[inline] def nextRng (x : UInt32) : UInt32 := x * 1664525 + 1013904223

/-- Scalar call with no allocation. It measures the bare call cost. -/
@[export smoke_add] def add (a b : UInt32) : UInt32 := a + b

/-- Deal a new game from a seed. -/
@[export smoke_new] def newGame (seed : UInt32) : State := Id.run do
  let mut rng := seed
  let mut cells : Array UInt32 := Array.mkEmpty numCells
  for _ in [0:numCells] do
    rng := nextRng rng
    cells := cells.push (1 + ((rng >>> 16) % 15))
  return { cells, scores := Array.replicate 4 0, seat := rng >>> 24 &&& 3, ply := 0, rng }

/-- The current seat claims a cell. A taken cell scores zero and the turn passes. -/
@[export smoke_step] def step (s : State) (action : UInt32) : State :=
  let i := action.toNat
  let v := s.cells[i]!
  let seat := s.seat.toNat
  { s with
    cells := s.cells.set! i 0
    scores := s.scores.modify seat (· + v)
    seat := (s.seat + 1) % numSeats
    ply := s.ply + 1
    rng := nextRng s.rng }

@[export smoke_current] def current (s : @& State) : UInt32 := s.seat
@[export smoke_done] def isDone (s : @& State) : UInt8 := if s.ply >= numPlies then 1 else 0
@[export smoke_score] def score (s : @& State) (seat : UInt32) : UInt32 := s.scores[seat.toNat]!

/-- One bit per legal cell. -/
@[export smoke_legal] def legalMask (s : @& State) : UInt32 := Id.run do
  let mut m : UInt32 := 0
  for i in [0:numCells] do
    if s.cells[i]! != 0 then
      m := m ||| ((1 : UInt32) <<< i.toUInt32)
  return m

/-- Observations for all four seats: cells, a my-turn flag, then scores from
that seat's point of view. 17 bytes for each seat. -/
@[export smoke_obs_all] def obsAll (s : @& State) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity 68
  for seat in [0:4] do
    for i in [0:numCells] do
      out := out.push s.cells[i]!.toUInt8
    out := out.push (if s.seat.toNat == seat then 1 else 0)
    for k in [0:4] do
      out := out.push s.scores[(seat + k) % 4]!.toUInt8
  return out

/-- Bot 0 claims a pseudo-random legal cell. -/
@[export smoke_bot_random] def botRandom (s : @& State) (seed : UInt32) : UInt32 := Id.run do
  let start := (nextRng (seed + s.rng)) >>> 16
  for k in [0:numCells] do
    let i := (start.toNat + k) % numCells
    if s.cells[i]! != 0 then
      return i.toUInt32
  return 0

/-- Bot 1 claims the largest cell. -/
@[export smoke_bot_greedy] def botGreedy (s : @& State) : UInt32 := Id.run do
  let mut best : UInt32 := 0
  let mut bestV : UInt32 := 0
  for i in [0:numCells] do
    if s.cells[i]! > bestV then
      bestV := s.cells[i]!
      best := i.toUInt32
  return best

end Smoke

import Charter.Words.State
import Charter.Sha256

/-!
# The seed, a new game and the dice

The server commits to its seed first. The players' nonces are then mixed in. After that, each roll
depends only on the seed and on how many rolls came before.
-/

namespace Charter

/-- The public fingerprint of the server's seed: the SHA-256 of its eight bytes, in hexadecimal.
The seed has only 64 bits and no salt, so a very large search could find it from this fingerprint. -/
def commitmentOf (serverSeed : UInt64) : String :=
  Sha256.toHex (Sha256.hash (Sha256.natBytes 8 serverSeed.toNat))

/-- The game's seed: the first eight bytes of the SHA-256 of the server's seed and the players'
nonces. -/
def combineSeed (serverSeed : UInt64) (nonces : List UInt64) : UInt64 :=
  let bytes := (serverSeed :: nonces).flatMap fun n => Sha256.natBytes 8 n.toNat
  ((Sha256.hash bytes).take 8).foldl (fun acc b => acc * 256 + b.toUInt64) 0

/-- A new game: `seats` players, all resources in the bank, nothing built, in setup, with the founding
laws in force. Proposal ids start after theirs. The server
commits to its seed, and the players' nonces are then mixed in to make the game's seed. This function
checks nothing. `Reachable.start` and `Engine.replay` require the limits on seats and nonces. -/
def initialState (G : GameDef) (seats : Nat) (serverSeed : UInt64) (nonces : List UInt64) :
    State G where
  turnOrder := List.range seats
  phase := .setup
  round := 1
  turnIndex := 0
  turnsTaken := 0
  rollsMade := 0
  lastRoll := none
  seed := combineSeed serverSeed nonces
  seedCommitment := commitmentOf serverSeed
  books := genesisBooks G
  journal := []
  pieces := []
  laws := G.startingLaws
  openProposals := []
  nextProposalId := G.foundingLaws.length
  deals := []
  dealsStarted := 0
  offers := []
  nextOfferId := 0
  builtThisRound := []
  actionsThisTurn := fun _ => 0
  declared := fun _ _ => 0
  eventsApplied := 0
  winner := none

/-- A standard, published way to scramble a number (splitmix64). -/
def scramble (x : UInt64) : UInt64 :=
  let a := x + 0x9E3779B97F4A7C15
  let b := (a ^^^ (a >>> 30)) * 0xBF58476D1CE4E5B9
  let c := (b ^^^ (b >>> 27)) * 0x94D049BB133111EB
  c ^^^ (c >>> 31)

/-- Die `i` of roll `k`. It depends only on the seed and the two counters. The seed is scrambled
first, so seeds `s` and `s + 1000` do not give the same rolls shifted by one. -/
def dieAt (G : GameDef) (seed : UInt64) (k i : Nat) : Nat :=
  let word := scramble (scramble seed + (UInt64.ofNat k) * 1000 + UInt64.ofNat i)
  word.toNat % G.diceSides + 1

/-- The total shown by roll number `k`. -/
def rollAt (G : GameDef) (seed : UInt64) (k : Nat) : Nat :=
  ((List.range G.diceCount).map (dieAt G seed k)).sum

end Charter

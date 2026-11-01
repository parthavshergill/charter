import Evolved.Pool
import Server.GenericCheck
import Server.Spec

/-!
# Every strategy in the pool names no pack

The build stops if a strategy the arena can seat reaches a pack, or holds a string that is not a weight's
name or a key of the log's JSON. `Server/GenericCheck.lean` says what the check covers and what it does not.
The three bad strategies at the end show that the check can fail.
-/

namespace Evolved.Generic
open Charter CharterServer CharterServer.Bots

/-- info: CharterServer.Bots.hand names no pack -/
#guard_msgs in
#check_generic CharterServer.Bots.hand

/-- info: CharterServer.Bots.Ctx.of names no pack -/
#guard_msgs in
#check_generic CharterServer.Bots.Ctx.of

/-- info: CharterServer.Bots.params names no pack -/
#guard_msgs in
#check_generic CharterServer.Bots.params

/-- info: Evolved.pool names no pack -/
#guard_msgs in
#check_generic Evolved.pool

/-! ## The check can fail -/

/-- A bad strategy: it plays as the hand bot, but holds on to a good by name. -/
def namesAGood : Strategy :=
  { name := "hand"
    decide := fun ctx s bots =>
      if bots.any fun b => bal s b "renown" > 0 then [] else hand.decide ctx s bots }

/-- error: Evolved.Generic.namesAGood is not generic: Evolved.Generic.namesAGood has the string "renown" -/
#guard_msgs in
#check_generic namesAGood

/-- A bad strategy: it plays as the hand bot, but stops when its game is one pack. -/
def readsAPack : Strategy :=
  { name := "hand"
    decide := fun {G} ctx s bots =>
      if G.rounds == Charter.Games.StrikeTheEarth.game.rounds then [] else hand.decide ctx s bots }

/--
error: Evolved.Generic.readsAPack is not generic: Evolved.Generic.readsAPack uses Charter.Games.StrikeTheEarth.game
-/
#guard_msgs in
#check_generic readsAPack

/-- A bad strategy: it plays as the hand bot, but only when there are six packs. -/
def countsPacks : Strategy :=
  { name := "hand"
    decide := fun ctx s bots => if gameSpecs.length == 6 then hand.decide ctx s bots else [] }

/--
error: Evolved.Generic.countsPacks is not generic: Evolved.Generic.countsPacks uses CharterServer.GameSpec; Evolved.Generic.countsPacks uses CharterServer.gameSpecs
-/
#guard_msgs in
#check_generic countsPacks

end Evolved.Generic

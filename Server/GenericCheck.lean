import Lean
import Server.BotCore
import Server.Spec

/-!
# A build check that the bot names no pack

The bot must play any pack, so it reads everything from the state and the rules. `#check_generic f` walks
every constant that `f` reaches, through the types and bodies of definitions. It fails the build if the walk
reaches a pack: a constant under `Charter.Games`, the list of packs, or anything whose type mentions
`GameSpec`. It also fails on a string in the bot's own code that is not on `approvedStrings`, such as the
name of a good or a piece. The end of this file runs it on what tables call, and shows it failing on three
bad bots. `ServerTests.lean` imports this file, so `lake build` runs the check.

This catches names and direct references to packs. It does not catch a rule tuned to one pack's shape,
such as `if G.targetPoints == 18`. It is a check at build time, not a proof, and no theorem of the game
depends on it.
-/

namespace CharterServer.GenericCheck
open Lean Elab Command

/-- Strings the bot's own code may hold: the keys of the log's JSON. -/
def approvedStrings : List String := ["t", "move", "seat", "vote", "id", "yes", "sign"]

/-- The modules that hold the bot's own code. A constant of the file being checked counts too. -/
def isBotModule (m : Name) : Bool :=
  m == `Server.BotCore || m == `Server.GameFacts

/-- This constant names a pack. -/
def namesAPack (c : Name) : Bool :=
  (`Charter.Games).isPrefixOf c || c == `CharterServer.gameSpecs || c == `CharterServer.specOf? ||
    c == `CharterServer.GameSpec

/-- The constants in a constant's type and, for a definition, its body. -/
def nextOf (env : Environment) (c : Name) : List Name :=
  match env.find? c with
  | some (.defnInfo d) => d.type.getUsedConstants.toList ++ d.value.getUsedConstants.toList
  | some (.opaqueInfo d) => d.type.getUsedConstants.toList ++ d.value.getUsedConstants.toList
  | some ci => ci.type.getUsedConstants.toList
  | none => []

/-- Every constant reachable from these, at most `fuel` steps on. `none` if the fuel runs out. -/
def walk (env : Environment) : Nat → List Name → NameSet → Option NameSet
  | _, [], seen => some seen
  | 0, _ :: _, _ => none
  | fuel + 1, c :: rest, seen =>
    if seen.contains c then walk env fuel rest seen
    else walk env fuel (nextOf env c ++ rest) (seen.insert c)

/-- The literals in an expression, in order, with each shared part counted every time it occurs. -/
def literals : Expr → List Literal
  | .lit l => [l]
  | .app f a => literals f ++ literals a
  | .lam _ t b _ | .forallE _ t b _ => literals t ++ literals b
  | .letE _ t v b _ => literals t ++ literals v ++ literals b
  | .mdata _ e | .proj _ _ e => literals e
  | _ => []

/-- The body of a definition, if this is one. -/
def bodyOf (env : Environment) (c : Name) : Option Expr :=
  match env.find? c with
  | some (.defnInfo d) => some d.value
  | some (.opaqueInfo d) => some d.value
  | _ => none

/-- This constant is part of a bot's own code. -/
def isOwn (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | none => true
  | some i => isBotModule (env.header.moduleNames[i.toNat]!)

/-- What is wrong with the code that `root` reaches. An empty list means nothing is. -/
def problems (env : Environment) (root : Name) : List String :=
  match walk env 10000000 [root] {} with
  | none => ["the walk is too long to finish"]
  | some seen =>
    let all := seen.toList
    let own := all.filter (isOwn env)
    -- Name the pack constants the bot's own code uses, or else one that the walk reached another way.
    let direct := own.flatMap fun c => ((nextOf env c).filter namesAPack).eraseDups.map fun x => s!"{c} uses {x}"
    let packs := match direct, all.filter namesAPack with
      | [], [] => []
      | [], x :: _ => [s!"it reaches a pack, such as {x}"]
      | ds, _ => ds
    let strings := own.flatMap fun c =>
      (((bodyOf env c).map literals).getD []).filterMap fun
        | .strVal s => if approvedStrings.contains s then none else some s!"{c} has the string \"{s}\""
        | .natVal _ => none
    packs ++ strings.eraseDups

/-- The numbers in the bot's own code that `root` reaches, by definition, to review by eye. Code that the
compiler writes, such as the cases of a `match`, is left out. -/
def numbers (env : Environment) (root : Name) : List (Name × List Nat) :=
  match walk env 10000000 [root] {} with
  | none => []
  | some seen =>
    (seen.toList.filter fun c =>
        isOwn env c && !c.isInternal && !Meta.isMatcherCore env c && !isAuxRecursor env c).filterMap fun c =>
      match ((((bodyOf env c).map literals).getD []).filterMap fun
          | .natVal n => some n
          | .strVal _ => none).eraseDups with
      | [] => none
      | ns => some (c, ns)

/-- `#check_generic s`: fail unless the code that `s` reaches names no pack and holds only approved
strings. -/
elab "#check_generic " id:ident : command => do
  let root ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  match problems (← getEnv) root with
  | [] => logInfo m!"{root} names no pack"
  | ps => logError m!"{root} is not generic: {"; ".intercalate ps}"

/-- `#bot_numbers s`: list the numbers in the bot's own code that `s` reaches. -/
elab "#bot_numbers " id:ident : command => do
  let root ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let ns := numbers (← getEnv) root
  logInfo m!"{ns.map fun x => s!"{x.1}: {x.2}"}"

end CharterServer.GenericCheck

/-! ## The bot at tables names no pack -/

namespace CharterServer.GenericCheck.Runs
open Charter CharterServer CharterServer.Bots

variable {G : GameDef}

/-- info: CharterServer.Bots.handEvents names no pack -/
#guard_msgs in
#check_generic CharterServer.Bots.handEvents

/-- info: CharterServer.Bots.Ctx.of names no pack -/
#guard_msgs in
#check_generic CharterServer.Bots.Ctx.of

/-! ## The check can fail -/

/-- A bad bot: it plays as the bot does, but holds on to a good by name. -/
def namesAGood (ctx : Ctx G) (s : State G) (bots : List Nat) : List Event :=
  if bots.any fun b => bal s b "renown" > 0 then [] else handEvents ctx s bots

/--
error: CharterServer.GenericCheck.Runs.namesAGood is not generic: CharterServer.GenericCheck.Runs.namesAGood has the string "renown"
-/
#guard_msgs in
#check_generic namesAGood

/-- A bad bot: it plays as the bot does, but stops when its game is one pack. -/
def readsAPack (ctx : Ctx G) (s : State G) (bots : List Nat) : List Event :=
  if G.rounds == Charter.Games.StrikeTheEarth.game.rounds then [] else handEvents ctx s bots

/--
error: CharterServer.GenericCheck.Runs.readsAPack is not generic: CharterServer.GenericCheck.Runs.readsAPack uses Charter.Games.StrikeTheEarth.game
-/
#guard_msgs in
#check_generic readsAPack

/-- A bad bot: it plays as the bot does, but only when there are six packs. -/
def countsPacks (ctx : Ctx G) (s : State G) (bots : List Nat) : List Event :=
  if gameSpecs.length == 6 then handEvents ctx s bots else []

/--
error: CharterServer.GenericCheck.Runs.countsPacks is not generic: CharterServer.GenericCheck.Runs.countsPacks uses CharterServer.GameSpec; CharterServer.GenericCheck.Runs.countsPacks uses CharterServer.gameSpecs
-/
#guard_msgs in
#check_generic countsPacks

end CharterServer.GenericCheck.Runs

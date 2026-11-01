import CharterRL.Env

/-!
# The C interface

These are the functions `rl/env/capi.c` calls. Each one takes its arguments over: the caller hands in a reference
and must not use it again. `capi.c` adds a reference before each call that only reads, so a C caller can keep its
game. Numbers come back as Lean arrays, and `capi.c` copies them into the caller's buffers.

An environment that could not be made, or not restarted, has `refused` set and no decision. `charter_rl_error` says
why.
-/

namespace CharterRL.Capi
open Lean CharterRL

/-- A game that never started. -/
private def broken : Env := { (default : Env) with refused := true, decision := .none }

/-- A new game from a JSON configuration, or `broken` if the configuration is wrong. -/
@[export charter_rl_make]
def make (cfg : String) : Env :=
  match Json.parse cfg >>= Env.ofJson with
  | .ok e => e
  | .error _ => broken

/-- What is wrong with this configuration, or nothing. -/
@[export charter_rl_error]
def error (cfg : String) : String :=
  match Json.parse cfg >>= Env.ofJson with
  | .ok _ => ""
  | .error msg => msg

/-- The same game's settings with a new lineup, written `a,b,c,d`, and a new seed. -/
@[export charter_rl_restart]
def restart (e : Env) (lineup : String) (seed : UInt64) : Env :=
  let plans := (lineup.splitOn ",").mapM readSeat
  match plans with
  | .error _ => broken
  | .ok plans =>
    if plans.length < e.T.minSeats || e.T.maxSeats < plans.length then broken else
    match Env.start e.T e.settings plans.toArray seed.toNat with
    | .ok e' => e'
    | .error _ => broken

@[export charter_rl_step]
def step (e : Env) (action : UInt32) : Env := e.step action.toNat

/-- The seat that must decide, or -1 when nobody must: the game is over or stuck. -/
@[export charter_rl_seat]
def seat (e : Env) : Int32 :=
  match e.decision.seat? with
  | some q => Int32.ofNat q
  | none => -1

/-- 1 when the game is over: it ended, or nothing can happen. -/
@[export charter_rl_over]
def over (e : Env) : UInt8 := if e.decision.seat?.isNone then 1 else 0

/-- 1 when the last step was refused, or the game never started. -/
@[export charter_rl_refused]
def refused (e : Env) : UInt8 := if e.refused then 1 else 0

/-- 1 when the seat that must decide is voting. -/
@[export charter_rl_voting]
def voting (e : Env) : UInt8 := match e.decision with | .vote .. => 1 | _ => 0

@[export charter_rl_obs]
def obs (e : Env) : FloatArray := e.observation

@[export charter_rl_mask]
def mask (e : Env) : ByteArray := e.mask

/-- Each seat's reward since the last action, `maxSeats` numbers. -/
@[export charter_rl_rewards]
def rewards (e : Env) : FloatArray := e.rewards

/-- Numbers about the game, in the order of `infoNames`. -/
@[export charter_rl_info]
def info (e : Env) : FloatArray := e.info

/-- What the named strategy would do now, as an action, or -1. -/
@[export charter_rl_suggest]
def suggest (e : Env) (name : String) : Int32 :=
  match e.suggest name with
  | some a => Int32.ofNat a
  | none => -1

/-- The game so far as a server log, one JSON event per line, with this table code and these seat names
(`a,b,c,d`). An error starts with `error: `. -/
@[export charter_rl_saved_log]
def savedLog (e : Env) (code names : String) : String :=
  match e.savedLog code (names.splitOn ",") with
  | .ok text => text
  | .error msg => s!"error: {msg}"

/-- After each event of the saved log: round, setup, laws in force, and each seat's points, one JSON list a line. -/
@[export charter_rl_saved_state]
def savedState (e : Env) : String := e.savedState

/-- How many seats this game has. -/
@[export charter_rl_seats]
def seats (e : Env) : UInt32 := UInt32.ofNat e.lineup.size

/-- The size of an observation under this game's settings. -/
@[export charter_rl_obs_size]
def obsSize (e : Env) : UInt32 := UInt32.ofNat (if e.settings.moveRows then fullSize else baseSize)

@[export charter_rl_act_size]
def actSizeC (_ : UInt32) : UInt32 := UInt32.ofNat actSize

@[export charter_rl_base_size]
def baseSizeC (_ : UInt32) : UInt32 := UInt32.ofNat baseSize

@[export charter_rl_full_size]
def fullSizeC (_ : UInt32) : UInt32 := UInt32.ofNat fullSize

@[export charter_rl_layout]
def layout (_ : UInt32) : String := layoutJson.pretty

/-- The names of `charter_rl_info`'s numbers, comma-separated. -/
@[export charter_rl_info_names]
def infoNamesC (_ : UInt32) : String := ",".intercalate infoNames

end CharterRL.Capi

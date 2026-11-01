import Std.Time
import Lean.Data.Json
import EventLog
import Server.Util

/-!
# What the server may spend

Strangers must not be able to spend the owner's API credit without limit. So the public server has two
budgets a day, in dollars, and every request to the API passes through `Formalize.runRequest`, which
asks this file first. A new route that calls Claude is covered with no work, because it cannot reach
the API any other way.

* `CHARTER_BUDGET_DAILY_USD`, 500 by default: the whole server.
* `CHARTER_BUDGET_PER_IP_USD`, 100 by default: one IP address. There are no accounts, so an IP address
  stands for a person. The server keeps only a salted hash of it, in memory, and never logs it.

The cost of a request is an estimate: the tokens the API reports, times the prices of the model it went
to. The check runs
before a request and the charge comes after it, so requests already running can pass a budget by a
little. When a budget is reached the game goes on, Claude seats pass their turns, and the clerk goes on
strike until the next day.

The server total and the count of new tables are written to a small log in the data folder, so the
mirror keeps them through a sleep. The per-IP figures are in memory, and a restart loses them.

`make sim` never calls `configure`, so its own runs have no budget.

A backup API key would go in `Formalize.settings`, which chooses the key, with `Formalize.failureOf`
naming the errors that should switch to it.
-/

namespace CharterServer.Spend
open Lean

/-- Dollars, as a whole number of millionths. -/
abbrev Micros := Nat

/-- Prices in millionths of a dollar for a million tokens. The defaults are the list prices of
`claude-opus-5-5`, the model the server uses unless told otherwise. -/
structure Prices where
  input : Micros := 4000000
  output : Micros := 20000000
  cacheRead : Micros := 200000
  cacheWrite : Micros := 5000000
  deriving Inhabited

/-- The list prices of `claude-haiku-5-5`, if it writes the law descriptions. That call uses no cache,
so the two cache prices are only estimates, at the same ratios as Opus. -/
def haikuPrices : Prices := { input := 100000, output := 500000, cacheRead := 5000, cacheWrite := 125000 }

/-- The list prices of `claude-sonnet-5-5`. -/
def sonnetPrices : Prices := { input := 2000000, output := 10000000, cacheRead := 200000, cacheWrite := 2500000 }

structure Settings where
  enabled : Bool := false
  daily : Micros := 500000000
  perIp : Micros := 100000000
  gamesPerDay : Nat := 500
  gamesPerIp : Nat := 100
  trustIpHeader : Bool := false
  /-- For Opus, and for any model with no prices of its own, so that an unknown model is not undercounted. -/
  prices : Prices := {}
  haiku : Prices := haikuPrices
  sonnet : Prices := sonnetPrices
  salt : String := ""
  deriving Inhabited

structure Counters where
  day : Nat := 0
  total : Micros := 0
  byIp : Std.HashMap UInt64 Micros := {}
  /-- Which address each table's spending counts against: the last to ask for Claude there. -/
  payer : Std.HashMap String UInt64 := {}
  games : Nat := 0
  gamesByIp : Std.HashMap UInt64 Nat := {}
  deriving Inhabited

initialize settingsRef : IO.Ref Settings ← IO.mkRef {}
initialize countersRef : IO.Ref Counters ← IO.mkRef {}
initialize ledgerRef : IO.Ref (Option (EventLog.Log String)) ← IO.mkRef none

/-- Read a decimal number of dollars, such as `12.50`, as millionths. -/
def parseDollars (s : String) : Option Micros := do
  match s.trimAscii.toString.splitOn "." with
  | [whole] => return (← whole.toNat?) * 1000000
  | [whole, frac] =>
    let frac6 := (frac ++ "000000").take 6 |>.toString
    let w ← if whole.isEmpty then some 0 else whole.toNat?
    return w * 1000000 + (← frac6.toNat?)
  | _ => none

/-- What these tokens cost, by estimate. -/
def costOf (p : Prices) (input cacheRead cacheWrite output : Nat) : Micros :=
  (input * p.input + cacheRead * p.cacheRead + cacheWrite * p.cacheWrite + output * p.output) / 1000000

/-- The prices of this model. -/
def Settings.pricesFor (s : Settings) (model : String) : Prices :=
  if model.startsWith "claude-haiku" then s.haiku
  else if model.startsWith "claude-sonnet" then s.sonnet
  else s.prices

#guard costOf ({} : Settings).haiku 1000000 0 0 1000000 == 600000
#guard costOf (({} : Settings).pricesFor "claude-haiku-5-5") 1000 0 0 100 == 150
#guard costOf (({} : Settings).pricesFor "claude-sonnet-5-5") 1000 0 0 100 == 3000
#guard costOf (({} : Settings).pricesFor "claude-opus-5-5") 1000 0 0 100 == 6000
#guard costOf (({} : Settings).pricesFor "a-model-from-next-year") 1000 0 0 100 == 6000
#guard parseDollars "500" == some 500000000
#guard parseDollars "0.20" == some 200000
#guard parseDollars ".5" == some 500000
#guard parseDollars "nonsense" == none
#guard costOf {} 1000000 0 0 1000000 == 24000000

def today : IO Nat := do
  let t ← Std.Time.Timestamp.now
  return (t.toSecondsSinceUnixEpoch.val / 86400).toNat

/-- The counters, with a new day's reset applied. -/
private def fresh : IO Unit := do
  let d ← today
  countersRef.modify fun c => if c.day == d then c else { payer := c.payer, day := d }

private def note (j : Json) : IO Unit := do
  if let some log ← ledgerRef.get then
    try discard <| log.append j.compress
    catch err => IO.eprintln s!"spend log: {err}"

/-- Turn the budgets on, from the environment. Called once by the server at start. -/
def configure (dataDir : System.FilePath) : IO Unit := do
  let usd (k : String) (d : Micros) : IO Micros := do
    return ((← IO.getEnv k).bind parseDollars).getD d
  let num (k : String) (d : Nat) : IO Nat := do
    return ((← IO.getEnv k).bind String.toNat?).getD d
  let base : Settings := {}
  let pricesFrom (name : String) (d : Prices) : IO Prices := do
    return { input := ← usd s!"CHARTER_PRICE_{name}INPUT_USD" d.input
             output := ← usd s!"CHARTER_PRICE_{name}OUTPUT_USD" d.output
             cacheRead := ← usd s!"CHARTER_PRICE_{name}CACHE_READ_USD" d.cacheRead
             cacheWrite := ← usd s!"CHARTER_PRICE_{name}CACHE_WRITE_USD" d.cacheWrite }
  settingsRef.set
    { enabled := true
      daily := ← usd "CHARTER_BUDGET_DAILY_USD" base.daily
      perIp := ← usd "CHARTER_BUDGET_PER_IP_USD" base.perIp
      gamesPerDay := ← num "CHARTER_GAMES_PER_DAY" base.gamesPerDay
      gamesPerIp := ← num "CHARTER_GAMES_PER_IP_DAY" base.gamesPerIp
      trustIpHeader := (← IO.getEnv "CHARTER_TRUST_CLIENT_IP").isSome
      prices := ← pricesFrom "" base.prices
      haiku := ← pricesFrom "HAIKU_" base.haiku
      sonnet := ← pricesFrom "SONNET_" base.sonnet
      salt := toHex (← randomBytes 16) }
  let log : EventLog.Log String ← EventLog.Log.open (dataDir / "_spend.ledger")
  ledgerRef.set (some log)
  let d ← today
  let mut c : Counters := { day := d }
  for row in ← log.readFrom 0 do
    if let .ok j := Json.parse row then
      if jNat j "day" == some d then
        c := { c with total := c.total + (jNat j "usd").getD 0, games := c.games + (jNat j "game").getD 0 }
  countersRef.set c

/-- The private key for a client's address. The proxy's header counts only when the owner says that a
proxy sets it, as the Worker does. With no proxy every client is the same person. -/
def keyOf (ipHeader : Option String) : IO UInt64 := do
  let s ← settingsRef.get
  let ip := if s.trustIpHeader then ipHeader.getD "unknown" else "local"
  return hash (s.salt ++ ip)

/-- Count this table's spending against this address from now on. -/
def setPayer (table : String) (ip : UInt64) : IO Unit :=
  countersRef.modify fun c => { c with payer := c.payer.insert table ip }

/-- What a player reads while a budget is used up. -/
def restingWords : String :=
  "The clerk is on strike until tomorrow! Sorry, that's on us. Claude seats will pass, but the rest of the game still works, and you can write a rule in formal text."

/-- Which budget stops Claude being called for this table now, for the server's log. `none` means go
ahead. The address is not named. -/
def whyResting (table : String) : IO (Option String) := do
  let s ← settingsRef.get
  if !s.enabled then return none
  fresh
  let c ← countersRef.get
  if c.total ≥ s.daily then return some "the server's budget for today is used up"
  if let some ip := c.payer.get? table then
    if c.byIp.getD ip 0 ≥ s.perIp then return some "one address's budget for today is used up"
  return none

/-- What the table reads if Claude must not be called for it now. `none` means go ahead. -/
def resting? (table : String) : IO (Option String) := do
  return (← whyResting table).map fun _ => restingWords

/-- Count what a finished request cost, at the prices of the model it went to. -/
def charge (table model : String) (input cacheRead cacheWrite output : Nat) : IO Unit := do
  let s ← settingsRef.get
  if !s.enabled then return
  let cost := costOf (s.pricesFor model) input cacheRead cacheWrite output
  if cost == 0 then return
  fresh
  countersRef.modify fun c =>
    let byIp := match c.payer.get? table with
      | some ip => c.byIp.insert ip (c.byIp.getD ip 0 + cost)
      | none => c.byIp
    { c with total := c.total + cost, byIp }
  note (Json.mkObj [("day", toJson (← today)), ("usd", toJson cost)])

/-- May this address found a new table? This is what stops the data folder growing without limit.
`none` means yes, and the table is counted. -/
def admitGame (ip : UInt64) : IO (Option String) := do
  let s ← settingsRef.get
  if !s.enabled then return none
  fresh
  let c ← countersRef.get
  if s.gamesPerDay != 0 && c.games ≥ s.gamesPerDay then
    return some "This server has founded all the tables it can today. Try again tomorrow."
  if s.gamesPerIp != 0 && c.gamesByIp.getD ip 0 ≥ s.gamesPerIp then
    return some "You have founded all the tables you can today. Try again tomorrow."
  countersRef.modify fun c =>
    { c with games := c.games + 1, gamesByIp := c.gamesByIp.insert ip (c.gamesByIp.getD ip 0 + 1) }
  note (Json.mkObj [("day", toJson (← today)), ("game", toJson (1 : Nat))])
  return none

end CharterServer.Spend

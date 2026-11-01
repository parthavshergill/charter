import Charter.Engine
import Charter.Games.Island
import Server.SExp

/-!
# The formal text of laws and deals

`parseProposal` reads `(law ...)` and `(deal ...)`, and `printProposal` writes them back. Adapted
from the older game's `Charter/Lang/Syntax.lean` to the new rule language. A player can type this
text, and it is what the event log stores. The checks here are only about the text. `lawProblems`
and `dealProblems` decide whether a law or a deal can pass.

Effects can nest at most two levels, such as a `for-each-player` holding an `if`.
-/

namespace Charter.Rules
open Charter SExp

abbrev P := Except String

private def fail {α : Type} (msg : String) (x : SExp) : P α := .error s!"This does not read as a rule: {msg}, at {x.render}."

/-- The resources of the Island, the default game. A game's own list goes to `parseProposal`. -/
def islandResources : List Res := Games.Island.island.resources.map (·.name)

/-- "a, b and c". -/
def wordsList : List String → String
  | [] => "nothing"
  | [a] => a
  | [a, b] => s!"{a} and {b}"
  | a :: rest => s!"{a}, {wordsList rest}"

def parseNat : SExp → P Nat
  | .num i => if 0 ≤ i then .ok i.toNat else .error s!"expected a natural number, got {i}"
  | x => fail "expected a number" x

def parseRes (rs : List Res) : SExp → P Res
  | .atom a => if rs.contains a then .ok a else .error s!"There is no resource called \"{a}\". The resources are {wordsList rs}."
  | x => fail "expected a resource" x

def parseResRef (rs : List Res) : SExp → P ResRef
  | .atom "res" => .ok .harvested
  | x => ResRef.lit <$> parseRes rs x

def parseKind : SExp → P PieceKind
  | .atom a => .ok a
  | x => fail "expected a piece name" x

def parseParty : SExp → P Party
  | .atom "actor" => .ok .actor
  | .atom "each" => .ok .each
  | .atom "treasury" => .ok .treasury
  | .atom "bank" => .ok .bank
  | .num _ => .error "The constitution forbids naming a player. Describe the situation instead, such as who holds what or who has built what."
  | .atom a => .error s!"A law can speak only of the acting player (actor), each player (each), the treasury or the bank, not \"{a}\". The constitution forbids naming a player."
  | x => fail "expected actor, each, treasury or bank" x

def parseBundle (rs : List Res) : SExp → P Bundle
  | .list (.atom "bundle" :: items) => items.mapM fun
      | .list [r, n] => do return (← parseRes rs r, ← parseNat n)
      | x => fail "expected (RESOURCE n)" x
  | x => fail "expected (bundle (RESOURCE n)...)" x

def parseExpr (rs : List Res) : SExp → P Expr
  | .num i => if 0 ≤ i then .ok (.lit i.toNat) else .error "negative number"
  | .atom "amount" => .ok .harvestedAmount
  | .list [.atom "holding", p, r] => return .holding (← parseParty p) (← parseResRef rs r)
  | .list [.atom "points", p] => return .points (← parseParty p)
  | .list [.atom "count", p, k] => return .count (← parseParty p) (← parseKind k)
  | .list [.atom "+", a, b] => return .add (← parseExpr rs a) (← parseExpr rs b)
  | .list [.atom "-", a, b] => return .sub (← parseExpr rs a) (← parseExpr rs b)
  | .list [.atom "*", a, b] => return .mul (← parseExpr rs a) (← parseExpr rs b)
  | .list [.atom "/", a, n] => return .div (← parseExpr rs a) (← parseNat n)
  | .list [.atom "min", a, b] => return .min (← parseExpr rs a) (← parseExpr rs b)
  | .list [.atom "max", a, b] => return .max (← parseExpr rs a) (← parseExpr rs b)
  | x => fail "bad number" x

def parseCond (rs : List Res) : SExp → P Cond
  | .atom "true" => .ok .yes
  | .list [.atom "<", a, b] => return .lt (← parseExpr rs a) (← parseExpr rs b)
  | .list [.atom "<=", a, b] => return .le (← parseExpr rs a) (← parseExpr rs b)
  | .list [.atom "=", a, b] => return .eq (← parseExpr rs a) (← parseExpr rs b)
  | .list [.atom "and", a, b] => return .and (← parseCond rs a) (← parseCond rs b)
  | .list [.atom "or", a, b] => return .or (← parseCond rs a) (← parseCond rs b)
  | .list [.atom "not", c] => return .not (← parseCond rs c)
  | .list [.atom "res-is", r] => return .harvestedIs (← parseRes rs r)
  | x => fail "bad condition" x

/-- A plain transfer. -/
def parseTransfer (rs : List Res) : SExp → P Effect
  | .list [.atom "transfer", f, t, r, e] =>
      return .transfer (← parseParty f) (← parseParty t) (← parseResRef rs r) (← parseExpr rs e)
  | x => fail "expected (transfer FROM TO RESOURCE AMOUNT)" x

/-- An effect at the inner level: a transfer, or an `if` holding transfers. -/
def parseInnerEffect (rs : List Res) : SExp → P Effect
  | .list (.atom "if" :: c :: body) => do
      let c ← parseCond rs c
      let b ← body.mapM (parseTransfer rs)
      if b.isEmpty then .error "if needs at least one transfer" else return .when c b
  | x => parseTransfer rs x

/-- An effect at the top of a clause. -/
def parseEffect (rs : List Res) : SExp → P Effect
  | .list (.atom "for-each-player" :: c :: body) => do
      let c ← parseCond rs c
      let b ← body.mapM (parseInnerEffect rs)
      if b.isEmpty then .error "for-each-player needs at least one effect" else return .forEach c b
  | x => parseInnerEffect rs x

def parseEffects1 (rs : List Res) (what : String) (xs : List SExp) : P (List Effect) := do
  let es ← xs.mapM (parseEffect rs)
  if es.isEmpty then .error s!"{what} needs at least one effect" else return es

def parsePlacement : SExp → P Placement
  | .atom "link" => .ok .link
  | .atom "spot" => .ok .spot
  | .list [.atom "upgrade", k] => return .upgrade (← parseKind k)
  | .list [.atom "attach", k] => return .attach (← parseKind k)
  | x => fail "expected link, spot, (upgrade PIECE) or (attach PIECE)" x

def parseClause (rs : List Res) : SExp → P Clause
  | .list (.atom "on-harvest" :: body) => .onHarvest <$> parseEffects1 rs "on-harvest" body
  | .list (.atom "on-build" :: k :: body) =>
      return .onBuild (← parseKind k) (← parseEffects1 rs "on-build" body)
  | .list (.atom "on-round-end" :: body) => .onRoundEnd <$> parseEffects1 rs "on-round-end" body
  | .list [.atom "set-cost", k, b] => return .setCost (← parseKind k) (← parseBundle rs b)
  | .list [.atom "set-points", k, n] => return .setPoints (← parseKind k) (← parseNat n)
  | .list [.atom "set-bank-rate", n] => return .setBankRate (← parseNat n)
  | .list [.atom "new-piece", .atom name, b, .list [.atom "points", n], pl,
      .list [.atom "yield", y], .list [.atom "limit", l]] =>
      return .newPiece { name := name, cost := ← parseBundle rs b, points := ← parseNat n
                         placement := ← parsePlacement pl, yield := ← parseNat y
                         limit := ← parseNat l }
  | .list [.atom "repeal", n] => return .repeal (← parseNat n)
  | x => fail "bad clause" x

def parseLaw (rs : List Res) : SExp → P Law
  | .list (.atom "law" :: .str title :: clauses) => do
      let cs ← clauses.mapM (parseClause rs)
      if cs.isEmpty then .error "a law needs at least one clause" else return { title, clauses := cs }
  | x => fail "expected (law \"title\" clause...)" x

def parsePayee : SExp → P Payee
  | .atom "treasury" => .ok .treasury
  | x => Payee.seat <$> parseNat x

def parsePay (rs : List Res) : SExp → P Pay
  | .list [.atom "pay", s, d, r, n] =>
      return { src := ← parseNat s, dst := ← parsePayee d, res := ← parseRes rs r, amount := ← parseNat n }
  | x => fail "expected (pay SEAT TO RESOURCE n)" x

def parseTerm (rs : List Res) : SExp → P Term
  | .list (.atom "every-round" :: ps) => .everyRound <$> ps.mapM (parsePay rs)
  | .list (.atom "on-build" :: s :: k :: ps) =>
      return .onBuild (← parseNat s) (← parseKind k) (← ps.mapM (parsePay rs))
  | .list (.atom "no-build" :: s :: k :: spots) =>
      return .noBuild (← parseNat s) (← parseKind k) (← spots.mapM parseNat)
  | .list [.atom "no-trade", a, b] => return .noTrade (← parseNat a) (← parseNat b)
  | x => fail "bad deal term" x

def parseDeposit (rs : List Res) : SExp → P (Seat × Res × Nat)
  | .list [s, r, n] => return (← parseNat s, ← parseRes rs r, ← parseNat n)
  | x => fail "expected (SEAT RESOURCE n)" x

def parseDeal (rs : List Res) : SExp → P Deal
  | .list (.atom "deal" :: .str title :: .list (.atom "signers" :: ss)
      :: .list [.atom "rounds", n] :: .list [.atom "exit-notice", e]
      :: .list (.atom "deposits" :: ds) :: terms) => do
      return { title, signers := ← ss.mapM parseNat, rounds := ← parseNat n
               exitNotice := ← parseNat e, deposits := ← ds.mapM (parseDeposit rs)
               terms := ← terms.mapM (parseTerm rs) }
  | x => fail "expected (deal \"title\" (signers ...) (rounds n) (exit-notice n) (deposits ...) term...)" x

/-- Read the text of a law or a deal. -/
def parseProposal (text : String) (rs : List Res := islandResources) : P Proposal := do
  match ← SExp.read text with
  | x@(.list (.atom "law" :: _)) => Proposal.law <$> parseLaw rs x
  | x@(.list (.atom "deal" :: _)) => Proposal.deal <$> parseDeal rs x
  | x => fail "expected (law ...) or (deal ...)" x

/-! ## Writing the text back -/

def natS (n : Nat) : SExp := .num n

def resRefS : ResRef → SExp
  | .lit r => .atom r
  | .harvested => .atom "res"

def partyS : Party → SExp
  | .actor => .atom "actor" | .each => .atom "each"
  | .treasury => .atom "treasury" | .bank => .atom "bank"

def bundleS (b : Bundle) : SExp :=
  .list (.atom "bundle" :: b.map fun x => .list [.atom x.1, natS x.2])

def exprS : Expr → SExp
  | .lit n => natS n
  | .harvestedAmount => .atom "amount"
  | .holding p r => .list [.atom "holding", partyS p, resRefS r]
  | .points p => .list [.atom "points", partyS p]
  | .count p k => .list [.atom "count", partyS p, .atom k]
  | .add a b => .list [.atom "+", exprS a, exprS b]
  | .sub a b => .list [.atom "-", exprS a, exprS b]
  | .mul a b => .list [.atom "*", exprS a, exprS b]
  | .div a n => .list [.atom "/", exprS a, natS n]
  | .min a b => .list [.atom "min", exprS a, exprS b]
  | .max a b => .list [.atom "max", exprS a, exprS b]

def condS : Cond → SExp
  | .yes => .atom "true"
  | .lt a b => .list [.atom "<", exprS a, exprS b]
  | .le a b => .list [.atom "<=", exprS a, exprS b]
  | .eq a b => .list [.atom "=", exprS a, exprS b]
  | .and a b => .list [.atom "and", condS a, condS b]
  | .or a b => .list [.atom "or", condS a, condS b]
  | .not c => .list [.atom "not", condS c]
  | .harvestedIs r => .list [.atom "res-is", .atom r]

mutual
  def effectS : Effect → SExp
    | .transfer f t r e => .list [.atom "transfer", partyS f, partyS t, resRefS r, exprS e]
    | .forEach c body => .list (.atom "for-each-player" :: condS c :: effectsS body)
    | .when c body => .list (.atom "if" :: condS c :: effectsS body)
  def effectsS : List Effect → List SExp
    | [] => []
    | e :: es => effectS e :: effectsS es
end

def placementS : Placement → SExp
  | .link => .atom "link" | .spot => .atom "spot"
  | .upgrade k => .list [.atom "upgrade", .atom k]
  | .attach k => .list [.atom "attach", .atom k]

def clauseS : Clause → SExp
  | .onHarvest b => .list (.atom "on-harvest" :: effectsS b)
  | .onBuild k b => .list (.atom "on-build" :: .atom k :: effectsS b)
  | .onRoundEnd b => .list (.atom "on-round-end" :: effectsS b)
  | .setCost k b => .list [.atom "set-cost", .atom k, bundleS b]
  | .setPoints k n => .list [.atom "set-points", .atom k, natS n]
  | .setBankRate n => .list [.atom "set-bank-rate", natS n]
  | .newPiece p =>
      .list [.atom "new-piece", .atom p.name, bundleS p.cost, .list [.atom "points", natS p.points],
        placementS p.placement, .list [.atom "yield", natS p.yield], .list [.atom "limit", natS p.limit]]
  | .repeal n => .list [.atom "repeal", natS n]

def lawS (l : Law) : SExp := .list (.atom "law" :: .str l.title :: l.clauses.map clauseS)

def payeeS : Payee → SExp
  | .seat s => natS s
  | .treasury => .atom "treasury"

def payS (p : Pay) : SExp := .list [.atom "pay", natS p.src, payeeS p.dst, .atom p.res, natS p.amount]

def termS : Term → SExp
  | .everyRound ps => .list (.atom "every-round" :: ps.map payS)
  | .onBuild s k ps => .list (.atom "on-build" :: natS s :: .atom k :: ps.map payS)
  | .noBuild s k spots => .list (.atom "no-build" :: natS s :: .atom k :: spots.map natS)
  | .noTrade a b => .list [.atom "no-trade", natS a, natS b]

def dealS (d : Deal) : SExp :=
  .list (.atom "deal" :: .str d.title :: .list (.atom "signers" :: d.signers.map natS)
    :: .list [.atom "rounds", natS d.rounds] :: .list [.atom "exit-notice", natS d.exitNotice]
    :: .list (.atom "deposits" :: d.deposits.map fun x => .list [natS x.1, .atom x.2.1, natS x.2.2])
    :: d.terms.map termS)

/-- The one-line text of a law or a deal. -/
def printProposal : Proposal → String
  | .law l => (lawS l).render
  | .deal d => (dealS d).render

/-! ## Sample laws

Each sample is flat, or has one `for-each-player`. -/

/-- A sample law: its id, and its formal text. -/
def sampleLaws : List (String × String) :=
  [ ("cheap-cities", "(law \"Cheaper cities\" (set-cost city (bundle (grain 2) (ore 2))))")
  , ("cheap-roads", "(law \"Free timber roads\" (set-cost road (bundle (brick 1))))")
  , ("bank-rate", "(law \"A fairer bank\" (set-bank-rate 3))")
  , ("harvest-tithe", "(law \"Harvest tithe\" (on-harvest (transfer actor treasury res (/ amount 2))))")
  , ("poor-relief", "(law \"Poor relief\" (on-round-end (for-each-player (<= (points each) 2) (transfer treasury each grain 1) (transfer treasury each wool 1))))")
  , ("build-gift", "(law \"City gift\" (on-build city (for-each-player true (transfer each actor grain 1))))")
  , ("road-toll", "(law \"Road toll\" (on-build road (transfer actor treasury timber 1)))")
  , ("settlement-worth", "(law \"Founders' honour\" (set-points settlement 2))")
  , ("lighthouse", "(law \"Lighthouses\" (new-piece lighthouse (bundle (ore 2) (brick 2)) (points 2) (attach settlement) (yield 1) (limit 2)))") ]

/-- The text for a simple deal form: `a` pays `b` each round, and `b` may pay `a` back. Deposits
are worked out here so that the deal covers what it could owe. -/
def formDeal (a b : Seat) (rounds exitNotice : Nat) (give : Res) (giveN : Nat)
    (get : Option (Res × Nat)) : Deal :=
  let pays : List Pay :=
    (if giveN == 0 then [] else [{ src := a, dst := .seat b, res := give, amount := giveN }]) ++
    (match get with
     | some (r, n) => if n == 0 then [] else [{ src := b, dst := .seat a, res := r, amount := n }]
     | none => [])
  { title := s!"A deal of {rounds} rounds"
    signers := [a, b]
    rounds := rounds
    exitNotice := exitNotice
    deposits := pays.map fun p => (p.src, p.res, rounds * p.amount)
    terms := [.everyRound pays] }

end Charter.Rules

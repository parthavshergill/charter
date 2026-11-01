import Server.Rules

/-!
# Which laws and deals the text can say

`Server/RoundTrip.lean` proves that a law or a deal reads back from its S-expression as the same value.
That is true of the laws and deals these checks accept. The checks follow the grammar of the parser.

The parser's own results always pass, as `readable_of_parse` proves. A `Law` written as a value in Lean
code might not. Four founding laws do not: `ServerTests.lean` names them.
-/

namespace Charter.Rules

namespace Readable

/-- The game has this resource. -/
def res (rs : List Res) (r : Res) : Bool := rs.contains r

/-- The game has this resource, and it is not called `res`. The word `res` means the resource the dice
just paid. -/
def resRef (rs : List Res) : ResRef → Bool
  | .lit r => r != "res" && res rs r
  | .harvested => true

mutual
  /-- Every resource in this number is real. A computed divisor is not a plain number, because
  `(/ a 2)` always reads as the fixed kind of division, `.div`. -/
  def expr (rs : List Res) : Expr → Bool
    | .lit _ | .harvestedAmount | .rolled | .round | .points _ | .count _ _ => true
    | .declared _ r | .holding _ r => resRef rs r
    | .add a b | .sub a b | .mul a b | .min a b | .max a b => expr rs a && expr rs b
    | .div a _ => expr rs a
    | .divBy _ (.lit _) => false
    | .divBy a b => expr rs a && expr rs b
    | .totalOver c a | .mostOver c a | .leastOver c a => cond rs c && expr rs a

  /-- Every resource in this test is real. -/
  def cond (rs : List Res) : Cond → Bool
    | .yes => true
    | .lt a b | .le a b | .eq a b => expr rs a && expr rs b
    | .and a b | .or a b => cond rs a && cond rs b
    | .not c => cond rs c
    | .harvestedIs r => res rs r
end

/-- A transfer, or a move of a piece. -/
def move (rs : List Res) : Effect → Bool
  | .transfer _ _ r a => resRef rs r && expr rs a
  | .movePiece .. => true
  | _ => false

/-- A move, or an `if` that holds at least one move. -/
def inner (rs : List Res) : Effect → Bool
  | .when c body => cond rs c && !body.isEmpty && body.all (move rs)
  | e => move rs e

/-- An effect at the top of a clause: `inner`, or a `for-each-player` that holds at least one `inner`.
So the text has no `if` around a `for-each-player`, and no effect inside two of the same kind. -/
def top (rs : List Res) : Effect → Bool
  | .forEach c body => cond rs c && !body.isEmpty && body.all (inner rs)
  | e => inner rs e

/-- At least one effect, and each one can be written. -/
def body (rs : List Res) (b : List Effect) : Bool := !b.isEmpty && b.all (top rs)

/-- Every resource in this price is real. -/
def bundle (rs : List Res) (b : Bundle) : Bool := b.all fun x => res rs x.1

/-- A clause the text can say. -/
def clause (rs : List Res) : Clause → Bool
  | .onHarvest b | .onRoundEnd b | .onRoll b | .now b | .onBuild _ b => body rs b
  | .setCost _ b => bundle rs b
  | .setPoints .. | .setBankRate _ | .repeal _ | .endGame => true
  | .setWorth r _ => res rs r
  | .newPiece p => bundle rs p.cost

/-- A law the text can say: at least one clause, and each one can be written. -/
def law (rs : List Res) (L : Law) : Bool := !L.clauses.isEmpty && L.clauses.all (clause rs)

/-- Every resource in this payment is real. -/
def pay (rs : List Res) (p : Pay) : Bool := res rs p.res

/-- Every resource in this promise is real. -/
def term (rs : List Res) : Term → Bool
  | .everyRound ps | .onBuild _ _ ps => ps.all (pay rs)
  | .noBuild .. | .noTrade .. => true

/-- Every resource in this deal is real. -/
def deal (rs : List Res) (d : Deal) : Bool :=
  d.deposits.all (fun x => res rs x.2.1) && d.terms.all (term rs)

/-- A law or a deal the text can say. -/
def proposal (rs : List Res) : Proposal → Bool
  | .law L => law rs L
  | .deal d => deal rs d

end Readable

end Charter.Rules

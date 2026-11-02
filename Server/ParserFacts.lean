import Server.ParserProof

/-!
# What the parser promises

People and Claude seats write laws and deals as text. The engine runs `Law` and `Deal` values, and the
constitution's theorems are about those values. `parseProposal` is the only step between the two.

The parser is the definition of the language. A text means what the parser makes of it, and no other
description of the language exists to compare it with. So these statements do not say the parser is
right. They cover what reading the parser alone cannot confirm:

- `nothing_gets_ignored`: the parser drops nothing it reads.
- `only_real_resources`: what it accepts names only resources the game has.

Both start from an S-expression, the tree the text becomes. Text to tree, `SExp.read`, is tested, not
proved. Two different texts can give one tree: spacing, comments, and `07` beside `7` make no difference.

These statements say nothing about the printer, which only affects what the screen shows. They also do
not say that a law can pass, or that a piece or a seat is real: the parser accepts any piece name and seat
number. `lawProblems` and `dealProblems` decide what can pass.
-/

namespace Charter.Rules
open Charter SExp

/-- **Nothing gets ignored.** If two S-expressions read as the same law or deal, they are the same
S-expression. So the result depends on every part of the S-expression, including the title: a parser that
dropped an argument or a clause would read two different S-expressions as one law. -/
theorem nothing_gets_ignored (rs : List Res) (x y : SExp) (p : Proposal)
    (hx : parseProposalSExp rs x = .ok p) (hy : parseProposalSExp rs y = .ok p) : x = y :=
  (parse_ok hx).1.symm.trans (parse_ok hy).1

/-- **A law uses only what the game has.** Every resource written in a law or a deal that the parser
accepts is in the game's list of resources. A law can still say `res`, which means whichever resource the
dice just paid. A law written directly in Lean, such as a founding law, does not come through the parser,
so this does not cover it. -/
theorem only_real_resources (rs : List Res) (x : SExp) (p : Proposal)
    (h : parseProposalSExp rs x = .ok p) : ∀ r ∈ resourcesNamed p, r ∈ rs :=
  (parse_ok h).2

/-! ## Examples -/

/-- A law's S-expression, with one clause. -/
def tollS : SExp :=
  .list [.atom "law", .str "Toll", .list [.atom "set-worth", .atom "ore", .num 1]]

/-- The law it reads as. -/
def toll : Law := { title := "Toll", clauses := [.setWorth "ore" 1] }

/-- Both statements on a real input, with each hypothesis met. -/
example : tollS = tollS := nothing_gets_ignored ["ore"] tollS tollS (.law toll) rfl rfl
example : "ore" ∈ ["ore"] := only_real_resources ["ore"] tollS (.law toll) rfl "ore" (by decide)

/-- A broken parser that keeps only the first clause of a law. -/
def firstClauseOnly (rs : List Res) : SExp → P Proposal
  | .list (head :: title :: clause :: _) => parseProposalSExp rs (.list [head, title, clause])
  | x => parseProposalSExp rs x

/-- The first statement rejects that parser: with a clause more, the S-expression reads as the same law. -/
example : ¬ ∀ x y p, firstClauseOnly ["ore"] x = .ok p → firstClauseOnly ["ore"] y = .ok p → x = y := by
  intro broken
  have := broken tollS (.list [.atom "law", .str "Toll", .list [.atom "set-worth", .atom "ore", .num 1],
    .list [.atom "end-game"]]) (.law toll) rfl rfl
  simp [tollS] at this

/-- The server reads text with these same functions. -/
example (text : String) (rs : List Res) :
    parseProposal text rs = (SExp.read text >>= parseProposalSExp rs) := rfl

end Charter.Rules

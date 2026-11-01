import Charter.Engine

/-!
# Plain sentences

The words the screen and the chronicle use, and the read-back of a deal from its terms. A deal names
seats and its terms are few, so its sentences here say what the terms say and nothing else. Nothing here
reads a title or any prose from Claude.

A law has no sentences here. Claude writes its description (`Server/Describe.lean`), or a pack does, and
the rule source below that is what counts.
-/

namespace Charter.Text
open Charter

/-! ## Words -/

/-- The plural of a piece name. -/
def pluralWord (k : String) : String :=
  match k.toList.reverse with
  | 'y' :: c :: _ =>
    if ['a', 'e', 'i', 'o', 'u'].contains c then k ++ "s"
    else String.ofList (k.toList.dropLast) ++ "ies"
  | 's' :: _ | 'x' :: _ => k ++ "es"
  | 'h' :: c :: _ => if c == 'c' || c == 's' then k ++ "es" else k ++ "s"
  | _ => k ++ "s"

def plural (n : Nat) (word : String) : String :=
  if n == 1 then s!"1 {word}" else s!"{n} {pluralWord word}"

def article (k : String) : String :=
  if ["a", "e", "i", "o", "u"].any (k.startsWith ·) then s!"an {k}" else s!"a {k}"

def capFirst (s : String) : String :=
  match s.toList with
  | [] => s
  | c :: cs => String.ofList (c.toUpper :: cs)

/-- "a", "a and b", "a, b and c". -/
def andList (xs : List String) : String :=
  match xs.reverse with
  | [] => ""
  | [x] => x
  | x :: rest => s!"{", ".intercalate rest.reverse} and {x}"

/-- "a", "a or b", "a, b or c". -/
def orList (xs : List String) : String :=
  match xs.reverse with
  | [] => ""
  | [x] => x
  | x :: rest => s!"{", ".intercalate rest.reverse} or {x}"

def bundleText (b : Bundle) : String :=
  match b with
  | [] => "nothing"
  | _ => andList (b.map fun x => s!"{x.2} {x.1}")

/-- "a 7", "an 8". -/
def rollName (n : Nat) : String :=
  if n == 8 || n == 11 || n == 18 then s!"an {n}" else s!"a {n}"

/-! ## Deals -/

def payeeText (names : Seat → String) : Payee → String
  | .seat s => names s
  | .treasury => "the treasury"

def payText (names : Seat → String) (p : Pay) : String :=
  s!"{names p.src} pays {payeeText names p.dst} {p.amount} {p.res}"

def corners : List Nat → String
  | [v] => s!"corner {v}"
  | vs => s!"corners {andList (vs.map toString)}"

def termLine (names : Seat → String) : Term → String
  | .everyRound [] => "Every round, no payment is made."
  | .everyRound ps => s!"Every round, {andList (ps.map (payText names))}."
  | .onBuild s k [] => s!"In a round when {names s} builds {article k}, no payment is made."
  | .onBuild s k ps =>
    s!"In a round when {names s} builds {article k}, {andList (ps.map (payText names))}."
  | .noBuild s k [] => s!"{names s} promises nothing about where to build {article k}."
  | .noBuild s k spots => s!"{names s} will not build {article k} at {corners spots}."
  | .noTrade a b => s!"{names a} will not trade with {names b}, in either direction."

/-- A deal as short lines, read back from its terms. -/
def dealLines (names : Seat → String) (d : Deal) : List String :=
  let head := s!"Between {andList (d.signers.map names)}, for {plural d.rounds "round"}."
  let deposits := d.deposits.map fun x => s!"{names x.1} sets aside {x.2.2} {x.2.1}"
  let dep := if deposits.isEmpty then []
    else [s!"{andList deposits}. What is left goes back when the deal ends."]
  let notice :=
    if d.exitNotice == 0 then "Any signer can end it at the end of a round."
    else if d.exitNotice == 1 then "Any signer can end it with 1 round's notice."
    else s!"Any signer can end it with {d.exitNotice} rounds' notice."
  [head] ++ d.terms.map (termLine names) ++ dep ++ [notice]

/-- A deal for the screen: one line for each thing it does. -/
def dealText (names : Seat → String) (d : Deal) : String := "\n".intercalate (dealLines names d)

/-- A deal on one line, for the chronicle. -/
def dealLine (names : Seat → String) (d : Deal) : String := " ".intercalate (dealLines names d)

/-- A move, as a label for a button. The bank's price comes from the rules in force. -/
def moveLabel (bankRate : Nat) : Move → String
  | .place k (.spot _) => s!"Build {article k} here"
  | .place k (.link _) => s!"Build {article k} here"
  | .bankTrade give get => s!"Trade {bankRate} {give} to the bank for 1 {get}"
  | .offer _ give get => s!"Offer {bundleText give} for {bundleText get}"
  | .accept _ => "Accept the offer"
  | .cancel _ => "Take back the offer"
  | .endTurn => "End turn"

end Charter.Text

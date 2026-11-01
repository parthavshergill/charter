import Charter.Engine

/-!
# Plain sentences

The screen reads laws and deals back from their clauses, because a law's title has no meaning in the
game. These sentences are the only description of a rule a player sees by default, so they say what
the clauses say and nothing else. Nothing here reads a title or any prose from Claude.

The aim is that a person would say it this way: "Each round, players with 3 or more points get 1 wool
from the bank." Where a shorter sentence would be wrong, the longer exact one wins. Each law is a list
of short lines, one for each thing it does. `lawText` keeps the lines apart for the screen, and
`lawLine` runs them together for the chronicle.

What the rule language means is in `Charter/Words/LawEffects.lean`. Four of its meanings shape the words:

- A payment from an account to itself moves nothing, so a player pays "every other player".
- `(- a b)` stops at 0, so it reads "their grain above 7". `(/ a n)` rounds down, and it says so.
- A party that does not exist at that moment (`actor` at a round's end) holds nothing and pays
  nothing. The sentence says so instead of pretending.
- A payer who is short pays in proportion. The law's last line says this, unless the payer is the
  bank or the law itself makes sure the payer can pay.
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

/-! ## What the words of a sentence point at -/

structure Ctx where
  /-- What to call the actor when "they" means someone else. -/
  actorNoun : String := "the acting player"
  hasActor : Bool := false
  hasEach : Bool := false
  hasHarvest : Bool := false
  /-- The party this sentence calls "they". -/
  they : Option Party := none
  /-- The resource just harvested, when the law's condition fixes it. -/
  known : Option Res := none

/-- This party exists at this moment. -/
def Ctx.bound (c : Ctx) : Party → Bool
  | .actor => c.hasActor
  | .each => c.hasEach
  | _ => true

def noun (c : Ctx) (p : Party) : String :=
  if c.they == some p then "they" else
  match p with
  | .actor => c.actorNoun
  | .each => "that player"
  | .treasury => "the treasury"
  | .bank => "the bank"

/-- The name of a party after a verb or "from". -/
def objectNoun (c : Ctx) (p : Party) : String :=
  if c.they == some p then "them" else noun c p

def possessive (c : Ctx) (p : Party) : String :=
  if c.they == some p then "their" else s!"{noun c p}'s"

def verbOf (c : Ctx) (p : Party) (base third : String) : String :=
  if c.they == some p then base else third

def isSeatParty : Party → Bool
  | .actor | .each => true
  | _ => false

/-- What a number reads as when a party it asks about does not exist at this moment. -/
def missingParty : Party → String
  | .actor => "0 (no player is acting here)"
  | _ => "0 (no player is picked here)"

/-! ## Numbers -/

/-- A number made of parts, which needs brackets inside another number. -/
def isCompound : Expr → Bool
  | .add .. | .sub .. | .mul .. | .div .. | .min .. | .max .. => true
  | _ => false

def wrap (e : Expr) (s : String) : String := if isCompound e then s!"({s})" else s

/-- A sum inside a sum, or a product inside a product, needs no brackets. -/
def wrapIn (same : Expr → Bool) (e : Expr) (s : String) : String :=
  if same e then s else wrap e s

def isAdd : Expr → Bool | .add .. => true | _ => false
def isMul : Expr → Bool | .mul .. => true | _ => false

/-- A single quantity. It reads as "their grain above 7". -/
def isQuantity : Expr → Bool
  | .holding .. | .points .. | .count .. | .harvestedAmount => true
  | _ => false

/-- This number reads as a plural noun: "their points are". -/
def isPluralExpr : Expr → Bool
  | .points p | .count p _ => isSeatParty p
  | _ => false

def fraction : Nat → Option String
  | 2 => some "half of"
  | 3 => some "a third of"
  | 4 => some "a quarter of"
  | _ => none

/-- The terms of a sum, flattened. -/
def sumTerms : Expr → List Expr
  | .add a b => sumTerms a ++ sumTerms b
  | e => [e]

/-- Three or more goods of one party added up, as a list: its party and the goods. -/
def holdingsSum (e : Expr) : Option (Party × List Res) :=
  match sumTerms e with
  | .holding p (.lit r) :: rest =>
    let others := rest.filterMap fun
      | .holding q (.lit x) => if q == p then some x else none
      | _ => none
    if others.length == rest.length && 2 ≤ rest.length then some (p, r :: others) else none
  | _ => none

def exprText (c : Ctx) : Expr → String
  | .lit n => toString n
  | .harvestedAmount =>
    if !c.hasHarvest then "0 (nothing was harvested here)"
    else if c.they == some .actor then "what they were paid"
    else s!"what {c.actorNoun} was paid"
  | .holding p r =>
    if !c.bound p then missingParty p else
    match r with
    | .lit x => s!"{possessive c p} {x}"
    | .harvested =>
      if c.hasHarvest then s!"{possessive c p} holding of that resource"
      else "0 (nothing was harvested here)"
  | .points p =>
    if !c.bound p then missingParty p
    else if isSeatParty p then s!"{possessive c p} points"
    else s!"0 ({noun c p} has no points)"
  | .count p k =>
    if !c.bound p then missingParty p
    else if isSeatParty p then s!"{possessive c p} {pluralWord k}"
    else s!"0 ({noun c p} owns no pieces)"
  | e@(.add a b) =>
    match holdingsSum e with
    | some (p, rs) =>
      if c.bound p then s!"{possessive c p} {andList rs} together"
      else s!"{wrapIn isAdd a (exprText c a)} plus {wrapIn isAdd b (exprText c b)}"
    | none => s!"{wrapIn isAdd a (exprText c a)} plus {wrapIn isAdd b (exprText c b)}"
  | .sub a b =>
    if isQuantity a then s!"{exprText c a} above {wrap b (exprText c b)}"
    else s!"{wrap a (exprText c a)} minus {wrap b (exprText c b)}, stopping at 0"
  | .mul (.lit 2) e => s!"twice {wrap e (exprText c e)}"
  | .mul e (.lit 2) => s!"twice {wrap e (exprText c e)}"
  | .mul (.lit n) e => s!"{n} times {wrap e (exprText c e)}"
  | .mul e (.lit n) => s!"{n} times {wrap e (exprText c e)}"
  | .mul a b => s!"{wrapIn isMul a (exprText c a)} times {wrapIn isMul b (exprText c b)}"
  | .div _ 0 => "0 (dividing by 0 gives 0)"
  | .div a 1 => exprText c a
  | .div a n =>
    match fraction n with
    | some f => s!"{f} {wrap a (exprText c a)}, rounded down"
    | none => s!"{wrap a (exprText c a)} divided by {n}, rounded down"
  | .min a b => s!"the smaller of {wrap a (exprText c a)} and {wrap b (exprText c b)}"
  | .max a b => s!"the larger of {wrap a (exprText c a)} and {wrap b (exprText c b)}"

/-! ## Conditions -/

/-- "c and d", with the two cases that need no words taken out. -/
def mkAnd : Cond → Cond → Cond
  | .yes, c | c, .yes => c
  | .not .yes, _ | _, .not .yes => .not .yes
  | a, b => .and a b

/-- "c or d", with the two cases that need no words taken out. -/
def mkOr : Cond → Cond → Cond
  | .yes, _ | _, .yes => .yes
  | .not .yes, c | c, .not .yes => c
  | a, b => .or a b

mutual
  /-- The same condition with `not` moved inward, so that it reads without "not (...)". -/
  def plainCond : Cond → Cond
    | .and a b => mkAnd (plainCond a) (plainCond b)
    | .or a b => mkOr (plainCond a) (plainCond b)
    | .not c => flipCond c
    | c => c

  /-- The opposite of a condition, with `not` moved inward. `not (a < b)` is `b ≤ a`. -/
  def flipCond : Cond → Cond
    | .yes => .not .yes
    | .lt a b => .le b a
    | .le a b => .lt b a
    | .eq a b => .not (.eq a b)
    | .and a b => mkOr (flipCond a) (flipCond b)
    | .or a b => mkAnd (flipCond a) (flipCond b)
    | .not c => plainCond c
    | .harvestedIs r => .not (.harvestedIs r)
end

/-- The conditions that must all hold. -/
def conjuncts : Cond → List Cond
  | .and a b => conjuncts a ++ conjuncts b
  | .yes => []
  | c => [c]

def allOf (cs : List Cond) : Cond := cs.foldr mkAnd .yes

/-- A thing a party has, which reads as a verb: "they hold more than 7 grain". -/
structure Measure where
  who : Party
  base : String
  third : String
  one : String
  many : String
  /-- Counted, like roads and points, not measured, like grain. -/
  counted : Bool

def measure (c : Ctx) : Expr → Option Measure
  | .holding p (.lit r) =>
    if c.bound p then some ⟨p, "hold", "holds", r, r, false⟩ else none
  | .points p =>
    if c.bound p && isSeatParty p then some ⟨p, "have", "has", "point", "points", true⟩ else none
  | .count p k =>
    if c.bound p && isSeatParty p then some ⟨p, "own", "owns", k, pluralWord k, true⟩ else none
  | _ => none

def Measure.unit (m : Measure) (n : Nat) : String := if n == 1 then m.one else m.many

/-- Two parties' amounts of the same thing, so they can be compared in one phrase. -/
def Measure.sameThing (a b : Measure) : Bool :=
  a.one == b.one && a.base == b.base && a.who != b.who

/-- One comparison about one party: who it is about, and the phrase after the verb. -/
structure Leaf where
  m : Measure
  phrase : String

/-- `a` is less than `b`. -/
def leafLt (c : Ctx) (a b : Expr) : Option Leaf :=
  match measure c a, b, measure c b, a with
  | some m, .lit n, _, _ =>
    some ⟨m, if n == 1 then s!"no {m.many}" else s!"fewer than {n} {m.many}"⟩
  | _, _, some m, .lit n =>
    some ⟨m, if n == 0 then s!"at least 1 {m.one}" else s!"more than {n} {m.unit n}"⟩
  | some ma, _, some mb, _ =>
    if !ma.sameThing mb then none
    else if c.they == some mb.who then
      some ⟨mb, s!"more {mb.many} than {objectNoun c ma.who}"⟩
    else
      some ⟨ma, s!"{if ma.counted then "fewer" else "less"} {ma.many} than {objectNoun c mb.who}"⟩
  | _, _, _, _ => none

/-- `a` is at most `b`. -/
def leafLe (c : Ctx) (a b : Expr) : Option Leaf :=
  match measure c a, b, measure c b, a with
  | some m, .lit n, _, _ =>
    some ⟨m, if n == 0 then s!"no {m.many}" else s!"at most {n} {m.unit n}"⟩
  | _, _, some m, .lit n =>
    some ⟨m, if n == 1 then s!"at least 1 {m.one}" else s!"{n} or more {m.many}"⟩
  | some ma, _, some mb, _ =>
    if !ma.sameThing mb then none
    else if c.they == some mb.who then
      some ⟨mb, s!"at least as {if mb.counted then "many" else "much"} {mb.many} as {objectNoun c ma.who}"⟩
    else
      some ⟨ma, s!"at most as {if ma.counted then "many" else "much"} {ma.many} as {objectNoun c mb.who}"⟩
  | _, _, _, _ => none

/-- `a` equals `b`. -/
def leafEq (c : Ctx) (a b : Expr) : Option Leaf :=
  match measure c a, b, measure c b, a with
  | some m, .lit n, _, _ | _, _, some m, .lit n =>
    some ⟨m, if n == 0 then s!"no {m.many}" else s!"exactly {n} {m.unit n}"⟩
  | some ma, _, some mb, _ =>
    if !ma.sameThing mb then none
    else
      let (x, y) := if c.they == some mb.who then (mb, ma) else (ma, mb)
      some ⟨x, s!"exactly as {if x.counted then "many" else "much"} {x.many} as {objectNoun c y.who}"⟩
  | _, _, _, _ => none

/-- `a` does not equal `b`. -/
def leafNe (c : Ctx) (a b : Expr) : Option Leaf :=
  match measure c a, b, measure c b, a with
  | some m, .lit n, _, _ | _, _, some m, .lit n =>
    some ⟨m, if n == 0 then s!"at least 1 {m.one}" else s!"anything but {n} {m.unit n}"⟩
  | _, _, _, _ => none

def leaf (c : Ctx) : Cond → Option Leaf
  | .lt a b => leafLt c a b
  | .le a b => leafLe c a b
  | .eq a b => leafEq c a b
  | .not (.eq a b) => leafNe c a b
  | _ => none

def isOr : Cond → Bool | .or .. => true | _ => false
def isAnd : Cond → Bool | .and .. => true | _ => false

/-- The words after "players with", when every part of the condition is about party `p`. -/
def withText (c : Ctx) (p : Party) : Cond → Option String
  | .and a b => do
    let x ← withText c p a
    let y ← withText c p b
    return s!"{if isOr a then s!"({x})" else x} and {if isOr b then s!"({y})" else y}"
  | .or a b => do
    let x ← withText c p a
    let y ← withText c p b
    return s!"{if isAnd a then s!"({x})" else x} or {if isAnd b then s!"({y})" else y}"
  | cond =>
    match leaf { c with they := some p } cond with
    | some l => if l.m.who == p then some l.phrase else none
    | none => none

/-- The condition as a clause of a sentence: "the treasury holds more than 5 grain". -/
def sentText (c : Ctx) : Cond → String
  | .yes => "always"
  | .harvestedIs r =>
    if c.hasHarvest then s!"the payment is {r}" else s!"the payment is {r} (never true here)"
  | .not .yes => "never"
  | .not (.harvestedIs r) =>
    if c.hasHarvest then s!"the payment is not {r}" else s!"the payment is not {r} (always true here)"
  | .and a b =>
    let x := sentText c a
    let y := sentText c b
    s!"{if isOr a then s!"({x})" else x} and {if isOr b then s!"({y})" else y}"
  | .or a b =>
    let x := sentText c a
    let y := sentText c b
    s!"{if isAnd a then s!"({x})" else x} or {if isAnd b then s!"({y})" else y}"
  | cond =>
    match leaf c cond with
    | some l =>
      let verb := verbOf c l.m.who l.m.base l.m.third
      s!"{noun c l.m.who} {verb} {l.phrase}"
    | none =>
      let isWord (e : Expr) := if isPluralExpr e then "are" else "is"
      match cond with
      | .lt (.lit n) b => s!"{exprText c b} {isWord b} more than {n}"
      | .lt a b => s!"{exprText c a} {isWord a} less than {exprText c b}"
      | .le a b => s!"{exprText c a} {isWord a} at most {exprText c b}"
      | .eq a b => s!"{exprText c a} {isWord a} equal to {exprText c b}"
      | .not (.eq a b) => s!"{exprText c a} {isWord a} not equal to {exprText c b}"
      | _ => "never"

/-! ## What a clause holds, flattened -/

/-- One transfer, with everything that decides whether it happens. Effects can nest, but a sentence
reads better with its conditions gathered up. Splitting a body this way does not change what it
does, because every transfer of a trigger is planned from the same moment and settled together. -/
structure Item where
  /-- Conditions of `for-each-player`s around the innermost one. The parser never makes these. -/
  outer : List Cond := []
  inEach : Bool := false
  /-- The condition of the `for-each-player` and any `if` inside it. -/
  eachCond : Cond := .yes
  /-- The `if`s around the transfer, outside any `for-each-player`. -/
  guards : Cond := .yes
  src : Party
  dst : Party
  res : ResRef
  amount : Expr

mutual
  def itemsOf (outer : List Cond) (inEach : Bool) (eachCond guards : Cond) : Effect → List Item
    | .transfer src dst res amount =>
      [{ outer, inEach, eachCond, guards, src, dst, res, amount }]
    | .forEach c body =>
      if inEach then itemsOfAll (outer ++ [eachCond]) true c guards body
      else itemsOfAll outer true c guards body
    | .when c body =>
      if inEach then itemsOfAll outer inEach (mkAnd eachCond c) guards body
      else itemsOfAll outer inEach eachCond (mkAnd guards c) body
  def itemsOfAll (outer : List Cond) (inEach : Bool) (eachCond guards : Cond) : List Effect → List Item
    | [] => []
    | e :: es => itemsOf outer inEach eachCond guards e ++ itemsOfAll outer inEach eachCond guards es
end

def _root_.Charter.Expr.mentionsEach : Expr → Bool
  | .holding .each _ | .points .each | .count .each _ => true
  | .add a b | .sub a b | .mul a b | .min a b | .max a b => a.mentionsEach || b.mentionsEach
  | .div a _ => a.mentionsEach
  | _ => false

def _root_.Charter.Cond.mentionsEach : Cond → Bool
  | .lt a b | .le a b | .eq a b => a.mentionsEach || b.mentionsEach
  | .and a b | .or a b => a.mentionsEach || b.mentionsEach
  | .not c => c.mentionsEach
  | _ => false

def substExpr (r : Res) : Expr → Expr
  | .holding p .harvested => .holding p (.lit r)
  | .add a b => .add (substExpr r a) (substExpr r b)
  | .sub a b => .sub (substExpr r a) (substExpr r b)
  | .mul a b => .mul (substExpr r a) (substExpr r b)
  | .div a n => .div (substExpr r a) n
  | .min a b => .min (substExpr r a) (substExpr r b)
  | .max a b => .max (substExpr r a) (substExpr r b)
  | e => e

def substCond (r : Res) : Cond → Cond
  | .lt a b => .lt (substExpr r a) (substExpr r b)
  | .le a b => .le (substExpr r a) (substExpr r b)
  | .eq a b => .eq (substExpr r a) (substExpr r b)
  | .and a b => .and (substCond r a) (substCond r b)
  | .or a b => .or (substCond r a) (substCond r b)
  | .not c => .not (substCond r c)
  | c => c

/-- The resources of a condition that only asks which resource was harvested. -/
def resOfOr : Cond → Option (List Res)
  | .harvestedIs r => some [r]
  | .or a b => do return (← resOfOr a) ++ (← resOfOr b)
  | _ => none

/-- The part of a condition that says which resource was harvested, as words after "is paid". -/
structure Harvested where
  /-- "ore", "ore or wool", "anything but ore". Empty when the condition does not limit it. -/
  words : String := ""
  /-- The one resource it must be. -/
  known : Option Res := none
  rest : List Cond := []

def harvestedOf (parts : List Cond) : Harvested :=
  let pos := parts.filterMap resOfOr
  let negs := parts.filterMap fun | .not (.harvestedIs r) => some r | _ => none
  let others := parts.filter fun c =>
    (resOfOr c).isNone && (match c with | .not (.harvestedIs _) => false | _ => true)
  match pos, negs with
  | [[r]], [] => { words := r, known := some r, rest := others }
  | [rs], [] => { words := orList rs, rest := others }
  | [], _ :: _ => { words := s!"anything but {orList negs}", rest := others }
  | _, _ => { rest := parts }

/-! ## Amounts -/

/-- "road they own", for "2 grain per road they own". -/
def perPhrase (c : Ctx) : Expr → Option String
  | .count p k =>
    if c.bound p && isSeatParty p then
      some s!"{k} {noun c p} {verbOf c p "own" "owns"}"
    else none
  | .points p =>
    if c.bound p && isSeatParty p then
      some s!"point {noun c p} {verbOf c p "have" "has"}"
    else none
  | .holding p (.lit y) =>
    if c.bound p then some s!"{y} {noun c p} {verbOf c p "hold" "holds"}" else none
  | _ => none

/-- What is paid, when the resource is the one just harvested: "half of it, rounded down". -/
def itAmount (c : Ctx) : Expr → String
  | .lit n => s!"{n} of it"
  | .harvestedAmount => "all of it"
  | .div _ 0 => "0 of it (dividing by 0 gives 0)"
  | .div .harvestedAmount 1 => "all of it"
  | .div .harvestedAmount n =>
    match fraction n with
    | some f => s!"{f} it, rounded down"
    | none => s!"an amount of it equal to what was paid divided by {n}, rounded down"
  | .sub .harvestedAmount (.lit n) => s!"all but {n} of it"
  | e => s!"an amount of it equal to {exprText c e}"

/-- The payer's own: "their" for a player, and "its" for the treasury or the bank. The payer is named
just before this word, so saying "the treasury pays all the treasury's grain" would read badly. -/
def payerOwn (c : Ctx) (p : Party) : String :=
  if c.they == some p || isSeatParty p then "their" else "its"

/-- What is paid, in words: "1 wool", "all their grain", "2 grain per settlement they own". -/
def amountText (c : Ctx) (src dst : Party) (r : ResRef) (e : Expr) : String :=
  match r with
  | .harvested => itAmount c e
  | .lit x =>
    let isKnown := c.known == some x && c.hasHarvest
    let usesAmount := match e with
      | .harvestedAmount | .div .harvestedAmount _ | .sub .harvestedAmount _ => true
      | _ => false
    if isKnown && usesAmount && src == .actor then itAmount c e
    else
    match e with
    | .lit n => s!"{n} {x}"
    | .harvestedAmount =>
      if isKnown && dst == .actor then s!"as much {x} again" else s!"{x} equal to {exprText c e}"
    | .holding p (.lit y) =>
      if !c.bound p then s!"{x} equal to {exprText c e}"
      else if y == x && p == src then s!"all {payerOwn c p} {x}"
      else if y == x then s!"as much {x} as {noun c p} {verbOf c p "hold" "holds"}"
      else s!"1 {x} per {y} {noun c p} {verbOf c p "hold" "holds"}"
    | .div (.holding p (.lit y)) n =>
      match fraction n with
      | some f =>
        if c.bound p && y == x && p == src then s!"{f} {payerOwn c p} {x}, rounded down"
        else s!"{x} equal to {exprText c e}"
      | none => s!"{x} equal to {exprText c e}"
    | .sub (.holding p (.lit y)) (.lit n) =>
      if c.bound p && y == x && p == src then s!"{payerOwn c p} {x} above {n}"
      else s!"{x} equal to {exprText c e}"
    | .min (.holding p (.lit y)) (.lit n) | .min (.lit n) (.holding p (.lit y)) =>
      if c.bound p && y == x && p == src then s!"up to {n} {x}"
      else s!"{x} equal to {exprText c e}"
    | .mul (.lit n) m | .mul m (.lit n) =>
      match perPhrase c m with
      | some per => s!"{n} {x} per {per}"
      | none => s!"{x} equal to {exprText c e}"
    | m =>
      match perPhrase c m with
      | some per => s!"1 {x} per {per}"
      | none => s!"{x} equal to {exprText c e}"

/-! ## Sentences -/

/-- What sets off a clause. -/
inductive Moment where
  | round
  | build (k : PieceKind)
  | harvest

def ctxFor : Moment → Ctx
  | .round => {}
  | .build _ => { actorNoun := "the builder", hasActor := true }
  | .harvest => { actorNoun := "the player paid", hasActor := true, hasHarvest := true }

/-- Why a transfer can never move anything, if it cannot. The parser accepts these. The constitution
rejects most of them, but the sentence must stay true for whatever the text says. -/
def deadReason (t : Moment) (x : Item) : Option String :=
  let c := ctxFor t
  let c := { c with hasEach := x.inEach }
  let bad (p : Party) : Option String :=
    if c.bound p then none else
    match p with
    | .actor => some "a round's end has no acting player"
    | _ => some "no player is picked here"
  match bad x.src, bad x.dst with
  | some r, _ | _, some r => some r
  | none, none =>
    if x.src == x.dst then
      some (match x.src with
        | .treasury => "the treasury would pay itself"
        | .bank => "the bank would pay itself"
        | _ => "a player would pay themselves")
    else
      match x.res with
      | .harvested => if c.hasHarvest then none else some "nothing was harvested here"
      | .lit _ => none

/-- The verb and the rest of a phrase about the sentence's subject, so that "get 1 grain from the
treasury" and "get 1 wool from the treasury" can join. -/
structure Phrase where
  verb : String
  amounts : List String
  tail : String

/-- An amount that ends in "rounded down" needs a comma before the words that follow it. -/
def closeAmount (a : String) : String := if a.endsWith "rounded down" then a ++ "," else a

/-- "half of their timber, rounded down" and so on, as one phrase, if every amount reads that way. -/
def halves (amounts : List String) : Option String :=
  let head := "half of their "
  let tail := ", rounded down"
  if amounts.length < 2 || !amounts.all (fun a => a.startsWith head && a.endsWith tail) then none
  else
    let names := amounts.map fun a => ((a.drop head.length).dropEnd tail.length).toString
    some s!"half of their {andList names}, each rounded down,"

def Phrase.render (plural : Bool) (p : Phrase) : String :=
  let amounts := match p.amounts.reverse with
    | [] => []
    | last :: rest => (closeAmount last :: rest).reverse
  let what := (halves p.amounts).getD (andList amounts)
  s!"{if plural then p.verb else p.verb ++ "s"} {what} {p.tail}"

/-- Join phrases that share a verb and a tail. -/
def joinPhrases (plural : Bool) (ps : List Phrase) : String :=
  let merged := ps.foldl (fun (acc : List Phrase) p =>
    match acc.getLast? with
    | some q =>
      if q.verb == p.verb && q.tail == p.tail then
        acc.dropLast ++ [{ q with amounts := q.amounts ++ p.amounts }]
      else acc ++ [p]
    | none => [p]) []
  " and ".intercalate (merged.map (Phrase.render plural))

/-- Who a line is about. -/
inductive Subject where
  /-- The players of a `for-each-player`. -/
  | each
  /-- The actor, paying or paid by the players of a `for-each-player`, or by an account. -/
  | actor
  /-- Neither: "the bank pays the treasury". -/
  | account
  deriving BEq

/-- Move the parts of a `for-each-player`'s condition that do not ask about the player out to the
`if`s: they do not depend on which player it is, and they read better in front. -/
def Item.tidy (x : Item) : Item :=
  if !x.inEach then { x with guards := plainCond x.guards } else
  let parts := conjuncts (plainCond x.eachCond)
  let stay := parts.filter Cond.mentionsEach
  let move := parts.filter (!·.mentionsEach)
  { x with eachCond := allOf stay, guards := mkAnd (plainCond x.guards) (allOf move) }

def subjectOf (t : Moment) (x : Item) : Subject :=
  let c := { (ctxFor t) with hasEach := x.inEach, they := some .each }
  let aboutEach := x.src == .each || x.dst == .each
  let aboutActor := c.hasActor && (x.src == .actor || x.dst == .actor)
  if aboutEach && aboutActor then
    if x.amount.mentionsEach || (withText c .each x.eachCond).isNone && x.eachCond != .yes then .each
    else .actor
  else if aboutEach then .each
  else if aboutActor && !x.inEach then .actor
  else .account

/-- "1 wool from the bank" as a phrase of `subject`. -/
def phraseOf (c : Ctx) (subject : Party) (others : String) (x : Item) : Phrase :=
  let amt := amountText c x.src x.dst x.res x.amount
  let name (p : Party) : String :=
    if p == .each then others else noun { c with they := none } p
  if x.src == subject then { verb := "pay", amounts := [amt], tail := s!"to {name x.dst}" }
  else { verb := "get", amounts := [amt], tail := s!"from {name x.src}" }

/-- What sets off a line, with the words that say which harvest. -/
structure Lead where
  /-- The start of the sentence, ending in a comma and a space, or empty. -/
  text : String
  /-- The subject when the actor is the subject. -/
  actor : String
  actorPlural : Bool

def leadOf (t : Moment) (actorWith : Option String) (resWords : String) : Lead :=
  match t with
  | .round => { text := "Each round, ", actor := "the acting player", actorPlural := false }
  | .build k =>
    let who := match actorWith with
      | some w => s!"anyone with {w} who builds {article k}"
      | none => s!"anyone who builds {article k}"
    { text := s!"Each time {article k} is built, ", actor := who, actorPlural := false }
  | .harvest =>
    let who := match actorWith with
      | some w => s!"a player with {w}"
      | none => "a player"
    let what := if resWords.isEmpty then "" else s!" {resWords}"
    { text := s!"Each time {who} is paid{what} at harvest, ", actor := "they", actorPlural := true }

/-- One line, for a run of transfers with the same conditions and the same subject. -/
def lineOf (t : Moment) (group : List Item) : String :=
  match group with
  | [] => ""
  | first :: _ =>
    let subject := subjectOf t first
    let base := { (ctxFor t) with hasEach := first.inEach }
    -- Which resource the harvest must be, from either kind of condition.
    let h : Harvested :=
      match t with
      | .harvest => harvestedOf (conjuncts first.guards ++ conjuncts first.eachCond)
      | _ => { rest := conjuncts first.guards ++ conjuncts first.eachCond }
    let known := h.known
    let subst (cond : Cond) : Cond := match known with
      | some r => substCond r cond
      | none => cond
    -- Outside a `for-each-player` no part belongs to one, even if it asks about `each`.
    let isEachPart (cond : Cond) := first.inEach && cond.mentionsEach
    let eachCond := subst (allOf (h.rest.filter isEachPart))
    let guards := subst (allOf (h.rest.filter (!isEachPart ·)))
    let items := group.map fun x =>
      match known, x.res with
      | some r, .harvested =>
        { x with res := .lit r, amount := substExpr r x.amount }
      | some r, _ => { x with amount := substExpr r x.amount }
      | none, _ => x
    let base := { base with known }
    -- An `if` about the actor alone joins the words about the actor.
    let actorWith : Option String :=
      if guards == .yes then none else
      match t with
      | .round => none
      | .build _ => if subject == .actor then withText base .actor guards else none
      | .harvest => withText base .actor guards
    let lead := leadOf t actorWith h.words
    let ifPart (c : Ctx) : String :=
      if guards == .yes || actorWith.isSome then "" else s!"if {sentText c guards}, "
    let actorLed := subject == .actor && (match t with | .build _ => true | _ => false)
    let leadText := if actorLed then "" else lead.text
    let outerText : String :=
      "".intercalate (first.outer.map fun o =>
        if o == .yes then "for each player, "
        else s!"for each player, if {sentText { base with they := some .each } o}, ")
    match subject with
    | .each =>
      let ce := { base with they := some .each }
      let aboutActor := group.any fun x => x.src == .actor || x.dst == .actor
      let single := aboutActor || eachCond == .yes
      let everyone := if aboutActor then "every other player" else "every player"
      match (if eachCond == .yes then some "" else withText base .each eachCond) with
      | some w =>
        let who :=
          if eachCond == .yes then everyone
          else if aboutActor then s!"{everyone} with {w}"
          else s!"players with {w}"
        let vp := joinPhrases (!single) (items.map (phraseOf ce .each who))
        s!"{leadText}{outerText}{ifPart base}{who} {vp}."
      | none =>
        let other := if aboutActor then "other " else ""
        let vp := joinPhrases true (items.map (phraseOf ce .each "them"))
        s!"{leadText}{outerText}{ifPart base}for each {other}player, if {sentText ce eachCond}, they {vp}."
    | .actor =>
      let ca := { base with they := some .actor }
      let others : String :=
        if eachCond == .yes then "every other player"
        else
          match withText base .each eachCond with
          | some w => s!"every other player with {w}"
          | none => "every other player"
      let vp := joinPhrases lead.actorPlural (items.map (phraseOf ca .actor others))
      let c := match t with
        | .harvest => ca
        | _ => base
      s!"{leadText}{ifPart c}{lead.actor} {vp}."
    | .account =>
      let parts := items.map fun x =>
        let c := { base with they := none }
        s!"{noun c x.src} pays {amountText c x.src x.dst x.res x.amount} to {objectNoun c x.dst}"
      let repeated : String :=
        if !first.inEach then "" else
        if eachCond == .yes then "for each player, "
        else
          match withText base .each eachCond with
          | some w => s!"for each player with {w}, "
          | none => s!"for each player, if {sentText { base with they := some .each } eachCond}, "
      let c := match t with
        | .harvest => { base with they := some .actor }
        | _ => base
      s!"{leadText}{outerText}{ifPart c}{repeated}{" and ".intercalate parts}."

/-- The start of a line that says nothing moves. -/
def plainLead : Moment → String
  | .round => "Each round, "
  | .build k => s!"Each time {article k} is built, "
  | .harvest => "Each time a player is paid at harvest, "

/-- Lines for a clause's effects. Runs of transfers with the same conditions and subject share one. -/
def linesOf (t : Moment) (body : List Effect) : List String :=
  let items := (itemsOfAll [] false .yes .yes body).map Item.tidy
  if items.isEmpty then [capFirst s!"{plainLead t}nothing happens."] else
  let groups : List (List Item) := items.foldl (fun (acc : List (List Item)) x =>
    match acc.getLast? with
    | some g =>
      match g.head? with
      | some y =>
        let same := y.outer == x.outer && y.inEach == x.inEach && y.eachCond == x.eachCond &&
          y.guards == x.guards && subjectOf t y == subjectOf t x &&
          (deadReason t y).isNone && (deadReason t x).isNone
        if same then acc.dropLast ++ [g ++ [x]] else acc ++ [[x]]
      | none => acc ++ [[x]]
    | none => [[x]]) []
  groups.map fun g =>
    let reason : Option String := match g with
      | x :: _ => deadReason t x
      | [] => none
    let never := g.any fun x => x.guards == .not .yes || x.eachCond == .not .yes
    match reason with
    | some r => capFirst s!"{plainLead t}nothing moves: {r}."
    | none =>
      if never then capFirst s!"{plainLead t}nothing moves: its condition is never true."
      else capFirst (lineOf t g)

/-! ## Can the payer always pay? -/

/-- The law makes sure holding of `p` in `r` is at least `n`, by a condition around the transfer. -/
def guardCovers (cs : List Cond) (p : Party) (r : ResRef) (n : Nat) : Bool :=
  cs.any fun
    | .lt (.lit m) (.holding q x) => q == p && x == r && n ≤ m + 1
    | .le (.lit m) (.holding q x) => q == p && x == r && n ≤ m
    | .eq (.holding q x) (.lit m) | .eq (.lit m) (.holding q x) => q == p && x == r && n ≤ m
    | _ => false

/-- This amount is never more than what `p` holds of `r`, because it is worked out from that. -/
def fromOwnHolding (p : Party) (r : ResRef) : Expr → Bool
  | .holding q x => q == p && x == r
  | .div (.holding q x) _ => q == p && x == r
  | .sub (.holding q x) _ => q == p && x == r
  | .min (.holding q x) _ | .min _ (.holding q x) => q == p && x == r
  | _ => false

/-- This amount is never more than what the actor was just paid. A harvest payment is at least 1,
because the bank's zero payments are dropped before laws react. -/
def fromHarvest : Expr → Bool
  | .harvestedAmount | .lit 1 | .lit 0 => true
  | .div .harvestedAmount _ | .sub .harvestedAmount _ => true
  | .min .harvestedAmount _ | .min _ .harvestedAmount => true
  | _ => false

/-- The clause alone cannot ask this payer for more than it holds. The bank is not listed: it starts
with all the resources, and a short bank is a rule of the whole game. -/
def itemCovered (t : Moment) (all : List Item) (x : Item) : Bool :=
  if x.src == .bank then true else
  let draws := (all.filter fun y => y.src == x.src && y.res == x.res).length
  if x.amount == .lit 0 then true
  else if 1 < draws then false
  else if x.inEach && x.src != .each then false
  else
    let parts := conjuncts x.guards ++ conjuncts x.eachCond
    match t with
    | .harvest =>
      let isHarvested := x.res == .harvested ||
        (match x.res with
         | .lit r => (harvestedOf parts).known == some r
         | _ => false)
      x.src == .actor && isHarvested && fromHarvest x.amount
    | _ =>
      fromOwnHolding x.src x.res x.amount ||
        (match x.amount with
         | .lit n => guardCovers parts x.src x.res n
         | _ => false)

/-- The law has a payment that can come up short, and a person would need to know what happens. -/
def clauseCanFallShort (t : Moment) (body : List Effect) : Bool :=
  let items := (itemsOfAll [] false .yes .yes body).map Item.tidy
  items.any fun x => (deadReason t x).isNone && !itemCovered t items x

def shortfallLine : String := "A payer who is short pays in proportion, rounded down."

/-! ## Clauses and laws -/

def placementSentence : Placement → String
  | .link => "Build it on a free side of a hex, next to your own pieces."
  | .spot => "Build it on a free corner your own pieces reach, with no piece on a corner next to it."
  | .upgrade k => s!"It replaces one of your {pluralWord k}."
  | .attach k => s!"Build it on one of your {pluralWord k}, which stays. Only one can go on each."

def pointsWords : Nat → String
  | 0 => "no points"
  | n => plural n "point"

def clauseLines : Clause → List String
  | .onHarvest b => linesOf .harvest b
  | .onBuild k b => linesOf (.build k) b
  | .onRoundEnd b => linesOf .round b
  | .setCost k [] => [s!"{capFirst (article k)} is free."]
  | .setCost k b => [s!"{capFirst (article k)} costs {bundleText b}."]
  | .setPoints k n => [s!"{capFirst (article k)} is worth {pointsWords n}."]
  | .setBankRate n => [s!"The bank trades {n} of a resource for 1 of another."]
  | .newPiece p =>
    let price := match p.cost with
      | [] => "It is free"
      | c => s!"It costs {bundleText c}"
    let harvest := match p.placement, p.yield with
      | .link, _ | _, 0 => "It collects nothing at harvest."
      | _, y => s!"When a hex it touches is rolled, it collects {y}."
    let limit := if p.limit == 0 then "No player can own one." else s!"Each player can own {p.limit}."
    [s!"New piece: the {p.name}. {price} and is worth {pointsWords p.points}. " ++
      s!"{placementSentence p.placement} {harvest} {limit}"]
  | .repeal n => [s!"Law {n} is repealed, and the rules it changed go back."]

def _root_.Charter.Clause.canFallShort : Clause → Bool
  | .onHarvest b => clauseCanFallShort .harvest b
  | .onBuild k b => clauseCanFallShort (.build k) b
  | .onRoundEnd b => clauseCanFallShort .round b
  | _ => false

/-- A law as short lines, read back from its clauses. -/
def lawLines (l : Law) : List String :=
  l.clauses.flatMap clauseLines ++
    (if l.clauses.any Clause.canFallShort then [shortfallLine] else [])

/-- A law for the screen: one line for each thing it does. -/
def lawText (l : Law) : String := "\n".intercalate (lawLines l)

/-- A law on one line, for the chronicle. -/
def lawLine (l : Law) : String := " ".intercalate (lawLines l)

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

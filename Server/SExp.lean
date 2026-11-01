/-!
# S-expressions: tokens, reader, writer

`SExp` is the concrete tree under the rule language. Integer-looking atoms
(`12`, `-3`) are read as `num`; double-quoted strings (with `\"` and `\\` escapes)
as `str`; `;` starts a comment to end of line.
-/

namespace Charter

inductive SExp where
  | atom (s : String)
  | num (i : Int)
  | str (s : String)
  | list (xs : List SExp)
  deriving Repr, Inhabited, BEq

namespace SExp

/-! ## Tokenizer -/

inductive Tok where
  | lp | rp
  | str (s : String)
  | atom (s : String)
  deriving Repr, BEq

private def isDelim (c : Char) : Bool :=
  c == '(' || c == ')' || c == '"' || c == ';' || c.isWhitespace

/-- Read the body of a string literal (after the opening quote). -/
private def readStr : List Char → List Char → Except String (String × List Char)
  | [], _ => .error "unterminated string literal"
  | '"' :: rest, acc => .ok (String.ofList acc.reverse, rest)
  | '\\' :: c :: rest, acc =>
      if c == '"' || c == '\\' then readStr rest (c :: acc)
      else if c == 'n' then readStr rest ('\n' :: acc)
      else .error s!"unknown escape \\{c}"
  | c :: rest, acc => readStr rest (c :: acc)

private def readAtom : List Char → List Char → String × List Char
  | [], acc => (String.ofList acc.reverse, [])
  | c :: rest, acc =>
      if isDelim c then (String.ofList acc.reverse, c :: rest) else readAtom rest (c :: acc)

private def skipLine : List Char → List Char
  | [] => []
  | '\n' :: rest => rest
  | _ :: rest => skipLine rest

/-- Tokenize with fuel; fuel = input length + 1 always suffices since each step consumes a char. -/
private def tokenizeAux : Nat → List Char → List Tok → Except String (List Tok)
  | 0, _, _ => .error "tokenizer: out of fuel"
  | _ + 1, [], acc => .ok acc.reverse
  | fuel + 1, c :: rest, acc =>
      if c == '(' then tokenizeAux fuel rest (.lp :: acc)
      else if c == ')' then tokenizeAux fuel rest (.rp :: acc)
      else if c == ';' then tokenizeAux fuel (skipLine rest) acc
      else if c.isWhitespace then tokenizeAux fuel rest acc
      else if c == '"' then
        match readStr rest [] with
        | .ok (s, rest') => tokenizeAux fuel rest' (.str s :: acc)
        | .error e => .error e
      else
        let (a, rest') := readAtom rest [c]
        tokenizeAux fuel rest' (.atom a :: acc)

def tokenize (s : String) : Except String (List Tok) :=
  tokenizeAux (s.length + 1) s.toList []

/-! ## Reader -/

/-- Parse an integer literal `-?[0-9]+`. -/
def parseInt? (s : String) : Option Int :=
  match s.toList with
  | '-' :: ds@(_ :: _) => if ds.all Char.isDigit then (String.ofList ds).toNat?.map (fun n => -(n : Int)) else none
  | ds@(_ :: _) => if ds.all Char.isDigit then (String.ofList ds).toNat?.map (fun n => (n : Int)) else none
  | [] => none

private def atomOf (a : String) : SExp :=
  match parseInt? a with
  | some i => .num i
  | none => .atom a

/-- Read a sequence of S-expressions until `)` (when `inList`) or end of input. -/
private def readSeq : Nat → Bool → List Tok → List SExp → Except String (List SExp × List Tok)
  | 0, _, _, _ => .error "reader: out of fuel"
  | _ + 1, inList, [], acc =>
      if inList then .error "missing ')'" else .ok (acc.reverse, [])
  | _ + 1, inList, .rp :: rest, acc =>
      if inList then .ok (acc.reverse, rest) else .error "unexpected ')'"
  | fuel + 1, inList, .lp :: rest, acc =>
      match readSeq fuel true rest [] with
      | .ok (xs, rest') => readSeq fuel inList rest' (.list xs :: acc)
      | .error e => .error e
  | fuel + 1, inList, .str s :: rest, acc => readSeq fuel inList rest (.str s :: acc)
  | fuel + 1, inList, .atom a :: rest, acc => readSeq fuel inList rest (atomOf a :: acc)

/-- Read all top-level S-expressions in a string. -/
def readAll (s : String) : Except String (List SExp) := do
  let toks ← tokenize s
  let (xs, _) ← readSeq (2 * toks.length + 2) false toks []
  return xs

/-- Read exactly one S-expression. -/
def read (s : String) : Except String SExp := do
  match ← readAll s with
  | [x] => return x
  | [] => throw "empty input"
  | _ => throw "expected exactly one top-level form"

/-! ## Writer -/

private def escape (s : String) : String :=
  s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\"" else if c == '\\' then acc ++ "\\\\"
    else if c == '\n' then acc ++ "\\n" else acc.push c) ""

/-- Render compactly on one line. -/
def render : SExp → String
  | .atom s => s
  | .num i => toString i
  | .str s => "\"" ++ escape s ++ "\""
  | .list xs => "(" ++ " ".intercalate (xs.attach.map fun ⟨x, _⟩ => render x) ++ ")"

end SExp
end Charter

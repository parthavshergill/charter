import Server.Rules

/-!
# The resources a law or a deal names

`resourcesNamed` lists every resource written in a law or a deal. `Rules.only_real_resources`, in
`Server/ParserFacts.lean`, says what the parser promises about this list.

The word `res` is not in the list: it means whichever resource the dice just paid, not a resource by name.
Pieces and seats are not resources, so they are not in the list either.
-/

namespace Charter.Rules

/-- The resource this names, if it names one. -/
def refNames : ResRef → List Res
  | .lit r => [r]
  | .harvested => []

mutual
  /-- The resources this number names. -/
  def exprNames : Expr → List Res
    | .lit _ | .harvestedAmount | .rolled | .round | .points _ | .count _ _ => []
    | .declared _ r | .holding _ r => refNames r
    | .add a b | .sub a b | .mul a b | .divBy a b | .min a b | .max a b => exprNames a ++ exprNames b
    | .div a _ => exprNames a
    | .totalOver c a | .mostOver c a | .leastOver c a => condNames c ++ exprNames a

  /-- The resources this test names. -/
  def condNames : Cond → List Res
    | .yes => []
    | .lt a b | .le a b | .eq a b => exprNames a ++ exprNames b
    | .and a b | .or a b => condNames a ++ condNames b
    | .not c => condNames c
    | .harvestedIs r => [r]
end

mutual
  /-- The resources this effect names. -/
  def effectNames : Effect → List Res
    | .transfer _ _ r a => refNames r ++ exprNames a
    | .movePiece .. => []
    | .forEach c body | .when c body => condNames c ++ effectsNames body

  /-- The resources these effects name. -/
  def effectsNames : List Effect → List Res
    | [] => []
    | e :: es => effectNames e ++ effectsNames es
end

/-- The resources this clause names. -/
def clauseNames : Clause → List Res
  | .onHarvest b | .onBuild _ b | .onRoundEnd b | .onRoll b | .now b => effectsNames b
  | .setCost _ b => b.map (·.1)
  | .setWorth r _ => [r]
  | .newPiece p => p.cost.map (·.1)
  | .setPoints .. | .setBankRate _ | .repeal _ | .endGame => []

/-- Every resource written in this law or deal. -/
def resourcesNamed : Proposal → List Res
  | .law L => L.clauses.flatMap clauseNames
  | .deal d => d.deposits.map (·.2.1) ++ d.allPays.map (·.res)

end Charter.Rules

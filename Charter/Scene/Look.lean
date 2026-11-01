/-!
# How a pack looks off the board

A pack's words, colours, fonts and drawn marks go to the browser as data. The browser checks every
value again and builds the elements itself (`web/look.js`). A pack never supplies JavaScript, shaders
or raw SVG. It can colour the voting panel, the preview numbers, the rule source and the constitution
page. It cannot reword or hide them.
-/

namespace Charter.Scene

/-- One shape of a drawn mark, on a 24 by 24 grid. `d` is SVG path data. A colour is `#rrggbb`, `none`
or `currentColor`. -/
structure IconPath where
  d : String
  fill : String := "none"
  stroke : String := "none"
  width : Float := 0
  opacity : Float := 1
  deriving Inhabited

/-- The base game's marks, drawn in `web/icons.js`, by the name of each resource and piece. -/
def islandMarks : List (String × String) :=
  [ ("grain", "grain"), ("timber", "timber"), ("ore", "ore"), ("wool", "wool"), ("brick", "brick")
  , ("road", "road"), ("settlement", "settlement"), ("city", "city") ]

structure Look where
  /-- The line under the title on the opening page. -/
  tagline : String := "Settle an island. Rewrite its rules. The constitution holds."
  /-- New values for the colour tokens at the top of `web/app.css`, such as ("vellum", "#efe4c8"). -/
  tokens : List (String × String) := []
  /-- A font from the fixed list in `web/look.js`. Empty keeps the default. -/
  bodyFont : String := ""
  displayFont : String := ""
  /-- This pack's own marks, by the name of a resource or a piece. -/
  icons : List (String × List IconPath) := []
  /-- A mark from `web/icons.js` for a name, for a pack that shares the built-in marks. -/
  marks : List (String × String) := islandMarks
  /-- Pieces the end screen does not count, because there are many and they say little. -/
  quietPieces : List String := ["road"]
  deriving Inhabited

end Charter.Scene

import Charter.Games.Omerta
import Charter.Scene.Render

/-! Placeholder look, for playtesting the rules only. -/

namespace Charter.Games.Omerta
open Charter.Scene

def theme : Theme :=
  { Scene.islandTheme with
    ground := fun
      | some "wine" => 0x6A1F3A
      | some "cement" => 0x8A8A86
      | some "fish" => 0x2A6F8F
      | _ => 0xC9B48A
    shape := fun k => if k == "front" then some .settlement else if k == "club" then some .city else none
    ownModel := fun k s => if k == "racket" then some (Scene.islandTheme.largeModel 7 s 0) else none
    look :=
      { Scene.islandTheme.look with
        tagline := "Everybody swears. Somebody talks."
        marks := [("wine", "grain"), ("cement", "brick"), ("fish", "wool"), ("cash", "relic"), ("dirt", "ore"),
                  ("street", "road"), ("front", "settlement"), ("club", "city"), ("racket", "knight")] } }

end Charter.Games.Omerta

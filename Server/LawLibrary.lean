import Server.Spec

/-!
# Laws for each game

A list of laws, as text, for each game. `Server/PreviewCheck.lean` tries them against the preview, and the
training environment in `rl/` puts them to a vote. It is in its own file so that the environment can use it without
the rest of the server.
-/

namespace CharterServer.PreviewCheck

/-- Laws to try, by game. They read holdings, act at a round's end, change prices, make pieces and react
to the roll. -/
def lawsFor (spec : GameSpec) : List String :=
  if spec.id == strikeSpec.id then
    [ "(law \"Half on a workshop\" (on-build workshop (transfer actor treasury ore (/ (holding actor ore) 2))))"
    , "(law \"Half on a tunnel\" (on-build tunnel (transfer actor treasury ember (/ (holding actor ember) 2))))"
    , "(law \"Half on a hall\" (on-build hall (transfer actor treasury fungus (/ (holding actor fungus) 2))))"
    , "(law \"Ember levy\" (on-round-end (for-each-player true (transfer each treasury ember (/ (holding each ember) 2)))))"
    , "(law \"Tithe\" (on-harvest (transfer actor treasury res (/ amount 2))))"
    , "(law \"Cheap tunnels\" (set-cost tunnel (bundle (stone 1))))"
    , "(law \"Danger pays\" (on-round-end (for-each-player (<= 3 (holding treasury danger)) (transfer bank each renown 1))))"
    , "(law \"Vaults\" (new-piece vault (bundle (stone 2) (ore 1)) (points 2) (attach hall) (yield 1) (limit 2)))" ]
  else if spec.id == slimeSpec.id then
    [ "(law \"Half on a swelling\" (on-build swelling (transfer actor treasury oatmeal (/ (holding actor oatmeal) 2))))"
    , "(law \"Half on a tendril\" (on-build tendril (transfer actor treasury dew (/ (holding actor dew) 2))))"
    , "(law \"Half on a node\" (on-build node (transfer actor treasury rot (/ (holding actor rot) 2))))"
    , "(law \"Rot levy\" (on-round-end (for-each-player true (transfer each treasury rot (/ (holding each rot) 2)))))"
    , "(law \"Tithe\" (on-harvest (transfer actor treasury res (/ amount 2))))"
    , "(law \"Cheap tendrils\" (set-cost tendril (bundle (oatmeal 1))))"
    , "(law \"Sporangia\" (new-piece sporangium (bundle (pollen 2) (rot 1)) (points 2) (attach node) (yield 1) (limit 2)))" ]
  else if spec.id == bubbleSpec.id then
    [ "(law \"Half on a campus\" (on-build campus (transfer actor treasury capital (/ (holding actor capital) 2))))"
    , "(law \"Half on a datacenter\" (on-build datacenter (transfer actor treasury capital (/ (holding actor capital) 2))))"
    , "(law \"Fibre tax\" (on-build fibre (transfer actor treasury concrete 1)))"
    , "(law \"Capital levy\" (on-round-end (for-each-player true (transfer each treasury capital (/ (holding each capital) 2)))))"
    , "(law \"Tithe\" (on-harvest (transfer actor treasury res (/ amount 2))))"
    , "(law \"Cheap fibre\" (set-cost fibre (bundle (concrete 1))))"
    , "(law \"Emergency audit\" (now (for-each-player true (transfer each bank hype (holding each hype))) (transfer treasury bank bubble (holding treasury bubble))))"
    , "(law \"Margin call\" (on-roll (for-each-player (<= 10 rolled) (transfer each treasury hype (/ (holding each hype) 2)))))"
    , "(law \"Bailout\" (on-round-end (for-each-player (< (points each) 5) (transfer bank each capital 3))))"
    , "(law \"Radomes\" (new-piece radome (bundle (silicon 2) (capital 2)) (points 2) (attach datacenter) (yield 1) (limit 2)))" ]
  else if spec.id == pirateSpec.id then
    [ "(law \"Half on a fort\" (on-build fort (transfer actor treasury powder (/ (holding actor powder) 2))))"
    , "(law \"Half on a sloop\" (on-build sloop (transfer actor treasury rum (/ (holding actor rum) 2))))"
    , "(law \"Rum levy\" (on-round-end (for-each-player true (transfer each treasury rum (/ (holding each rum) 2)))))"
    , "(law \"Tithe\" (on-harvest (transfer actor treasury res (/ amount 2))))"
    , "(law \"Cheap sloops\" (set-cost sloop (bundle (timber 1))))"
    , "(law \"Roller's gift\" (on-roll (transfer bank actor rum 1)))"
    , "(law \"Sack on a 7\" (on-roll (for-each-player (and (= rolled 7) (< (points actor) (points each))) (move-piece each actor wharf))))"
    , "(law \"Lighthouses\" (new-piece lighthouse (bundle (powder 2) (timber 2)) (points 2) (attach wharf) (yield 1) (limit 2)))" ]
  else
    [ "(law \"Half on a city\" (on-build city (transfer actor treasury grain (/ (holding actor grain) 2))))"
    , "(law \"Half on a road\" (on-build road (transfer actor treasury timber (/ (holding actor timber) 2))))"
    , "(law \"Half on a settlement\" (on-build settlement (transfer actor treasury grain (/ (holding actor grain) 2))))"
    , "(law \"Wool levy\" (on-round-end (for-each-player true (transfer each treasury wool (/ (holding each wool) 2)))))"
    , "(law \"Dole and tithe\" (on-round-end (for-each-player true (transfer bank each grain 1))) (on-harvest (if (< 1 (holding actor grain)) (transfer actor treasury grain 1))))"
    , "(law \"Tithe\" (on-harvest (transfer actor treasury res (/ amount 2))))"
    , "(law \"Cheap cities\" (set-cost city (bundle (grain 2) (ore 2))))"
    , "(law \"Roller's gift\" (on-roll (transfer bank actor grain 1)))"
    , "(law \"Half on a 7\" (on-roll (for-each-player (and (= rolled 7) (< 3 (+ (holding each grain) (holding each wool)))) (transfer each treasury grain (/ (holding each grain) 2)) (transfer each treasury wool (/ (holding each wool) 2)))))"
    , "(law \"Roll tithe\" (on-roll (for-each-player (<= 7 rolled) (transfer each treasury grain (/ (holding each grain) 2)))))"
    , "(law \"Lighthouses\" (new-piece lighthouse (bundle (ore 2) (brick 2)) (points 2) (attach settlement) (yield 1) (limit 2)))" ]

end CharterServer.PreviewCheck

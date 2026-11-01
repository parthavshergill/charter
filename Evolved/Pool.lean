import Server.BotCore

/-!
# The strategies the arena can seat

To add a strategy, add its module here and to the list. `docs/arena.md` shows how.
-/

namespace Evolved
open CharterServer

/-- The strategies the arena can seat. -/
def pool : List Bots.Strategy := [Bots.hand]

end Evolved

import Lobby

/-! Concrete scenario checks, evaluated by `#guard` at build time. -/

open Lobby

namespace Lobby.Tests

def l0 : Lobby := (Lobby.empty.step (.create "ABCD" 2 3)).1

#guard (Lobby.empty.step (.create "ABCD" 2 3)).2 == [.created "ABCD"]
#guard (l0.step (.create "ABCD" 2 3)).2 == [.rejected "ABCD" .duplicateCode]
#guard (l0.step (.create "ABCD" 2 3)).1 == l0
#guard (Lobby.empty.step (.create "X" 0 3)).2 == [.rejected "X" (.badSeatRange 0 3)]
#guard (Lobby.empty.step (.create "X" 4 3)).2 == [.rejected "X" (.badSeatRange 4 3)]
#guard (l0.step (.join "NOPE" "ann" "t1")).2 == [.rejected "NOPE" .noSuchRoom]

def l1 : Lobby := (l0.run [.join "ABCD" "ann" "t1", .join "ABCD" "bob" "t2"]).1

#guard (l0.run [.join "ABCD" "ann" "t1", .join "ABCD" "bob" "t2"]).2 ==
  [.joined "ABCD" 0 "ann", .joined "ABCD" 1 "bob"]
-- same token twice is rejected
#guard (l1.step (.join "ABCD" "eve" "t1")).2 == [.rejected "ABCD" .tokenInUse]
-- leaving before start frees the seat, and the next join takes the lowest free seat
#guard (l1.run [.leave "ABCD" "t1", .join "ABCD" "cat" "t3"]).2 ==
  [.left "ABCD" 0, .joined "ABCD" 0 "cat"]
-- start needs min seats
#guard ((l0.run [.join "ABCD" "ann" "t1", .start "ABCD"]).2) ==
  [.joined "ABCD" 0 "ann", .rejected "ABCD" (.notEnoughPlayers 1 2)]
#guard (l1.step (.start "ABCD")).2 == [.started "ABCD" 2]

def l2 : Lobby := (l1.step (.start "ABCD")).1

#guard (l2.step (.start "ABCD")).2 == [.rejected "ABCD" .alreadyStarted]
#guard (l2.step (.join "ABCD" "cat" "t3")).2 == [.rejected "ABCD" .alreadyStarted]
-- after start, leave keeps the seat; reconnect restores it
#guard (l2.step (.leave "ABCD" "t2")).2 == [.disconnected "ABCD" 1]
#guard ((l2.step (.leave "ABCD" "t2")).1.step (.reconnect "ABCD" "t2")).2 ==
  [.reconnected "ABCD" 1 "bob"]
#guard ((l2.step (.leave "ABCD" "t2")).1.step (.reconnect "ABCD" "t2")).1 == l2
#guard (l2.step (.reconnect "ABCD" "zz")).2 == [.rejected "ABCD" .unknownToken]

-- full room
def l3 : Lobby := (l1.step (.join "ABCD" "cat" "t3")).1
#guard ((l3.room? "ABCD").map (·.isFull)) == some true
#guard (l3.step (.join "ABCD" "dan" "t4")).2 == [.rejected "ABCD" .roomFull]
#guard ((l3.room? "ABCD").map (·.filled)) == some 3

-- rooms are independent: the same token may sit in two different rooms
#guard ((l1.run [.create "EFGH" 2 2, .join "EFGH" "ann" "t1"]).2) ==
  [.created "EFGH", .joined "EFGH" 0 "ann"]

-- README quickstart
#guard (Lobby.empty.run [.create "ABCD" 2 4, .join "ABCD" "ann" "tok-ann",
    .join "ABCD" "bob" "tok-bob", .start "ABCD", .leave "ABCD" "tok-bob",
    .reconnect "ABCD" "tok-bob"]).2 ==
  [.created "ABCD", .joined "ABCD" 0 "ann", .joined "ABCD" 1 "bob",
   .started "ABCD" 2, .disconnected "ABCD" 1, .reconnected "ABCD" 1 "bob"]

end Lobby.Tests

# Making a reskin

A reskin is a pack with its own look. Lean still sends commands to the JavaScript player, and packs still compile into the server. There are no proofs about skins. Plain build checks stand in for them. Agents are trusted, but a pack never supplies JavaScript, shaders or raw SVG.

`Charter/Games/SlimeParliament.lean` is the worked example.

## What a pack may change

A pack's `Theme` holds all of this:

- The board: tile tops, what stands on tiles, what lies around the map, the treasury, the square, monuments, and every piece model.
- The seat colours.
- The screen, through `Theme.look`: the tagline on the scroll, the colour tokens at the top of `web/app.css`, fonts from the fixed list in `web/look.js`, and icons as path data and colours. The word Charter on the scroll keeps its own face. The browser checks all of these again and sets them with `setAttribute`.
- The 2D board's colours, through `Theme.flat`.
- The world's music, through `Theme.look`: `music` names a loop in `web/audio/music`. A pack with none gets the default. To add a loop, write it in `scripts/sound/render.py` and add its name to `musicTracks` in `Charter/Scene/LookCheck.lean`. The sound effects are the same in every world.

A pack can colour the voting panel, the preview numbers, the rule source and the constitution page. It cannot reword or hide them. The screen's structure and move flows do not change. The board stays a hex layout: pieces stand on the corners, and links lie on the sides.

## Steps

1. Copy the shape of `Charter/Games/SlimeParliament.lean`: hexes, resources, pieces, founding laws, and a `GameDef` with `theorem my_valid : my.Valid := by decide +kernel`.
2. Name goods with mass nouns, such as "oatmeal" or "dew". The rule text says "pays 1 oatmeal", and it does not change a word to its singular.
3. Make the meshes however you like. They go in `packs/<pack>/meshes/<sha256>.mesh`. The format is in `packages/lean-gpu-cmd/WIRE.md`. `packs/slime-parliament/gen.py` is one way to make them. Copy it if it helps. It also writes the Lean table of ids and hashes. Never edit that table by hand.
4. Write the `Theme`. A model that shows its owner is a painted mesh drawn in white and a white mesh drawn in the seat's colour, because a draw's colour multiplies the vertex colours. Give it a second cue that differs by seat, as colour should not be the only one.
5. Add a `GameSpec` to the end of `gameSpecs` in `Server/Spec.lean`, with a `meshFolder`. Import the pack in `Charter.lean`. A new pack shows in the Library, because `web/app.js` names the base games. To give its Claude seats their own names and voices, add a cast to `casts` in `Server/Persona.lean`.
6. Run `lake build Server.Spec`. The check at the end of that file prints what the pack lacks, in words, and stops the build. Fix what it names.
7. Run `make contact-sheet PACK=<id>`, and read the image in `contact-sheets/`. It shows each model in each seat's colour, every tile top, every monument, and models together on tiles, at the size a game draws them. Look for models that look alike, an owner's colour you cannot see, and anything covering a number token. Fix those, and draw it again.
8. If the pack has founding laws, write what each one does in the pack's own words, as in `Charter/Games/SlimeParliamentWords.lean`, and set `foundingWords`. A founding law with no words shows its source with a short note. `ServerTests.lean` prints each law's fingerprint.
9. Add a set of laws for the pack to `lawsFor` in `Server/PreviewCheck.lean`, and add its id to the list in `scripts/smoke.py` and in `ServerTests.lean`.
10. Play it with bots, look at it in a browser, and run `make audit`, `make smoke`, `make clerk-check` and `make deploy-check`.

## The budgets

Measured on a Slime Parliament game at round 8, with its 32 mesh files loaded, and a copy of the whole scene added for the larger rows. Each frame was timed through to the finished picture. The Island row is the same machine at a late stage of a game.

| Machine | Scene | Frame, shadows kept | Frame, shadows redrawn |
|---|---|---|---|
| Apple M4 Pro, 2880 by 1800 | 102,000 triangles, 324 draws | 5.1 ms | 4.6 ms |
| The same | 204,000 triangles, 648 draws | 4.5 ms | 4.9 ms |
| The same | 816,000 triangles, 2,592 draws | 8.4 ms | 9.7 ms |
| Software rendering, 1440 by 813 | 102,000 triangles, 324 draws | 101 ms | 126 ms |
| The same | 204,000 triangles, 648 draws | 176 ms | 211 ms |
| The same | 408,000 triangles, 1,296 draws | 304 ms | 377 ms |
| Software rendering, the Island | 71,000 triangles, 1,429 draws | 96 ms | 132 ms |

Software rendering is the worst case: a machine with no working graphics chip. No integrated graphics chip was measured. A real game of this pack costs about what the Island costs there, and a board at the scene cap costs about 1.8 times as much. So these are the caps, in `Charter/Scene/LookCheck.lean`:

- 5,000 mesh file triangles for one piece's model.
- 200,000 mesh file triangles for a full board: every piece to its limit for four seats, and 16 monuments. The build check draws that board and counts.
- 12,000 triangles in any one mesh file. The player refuses a larger file, in `web/vendor/meshfile.js`.

Something that repeats costs more than something large. A pack's link piece is usually the most repeated thing on the board.

A mesh with motion makes the player draw 30 frames a second while the scene shows. Its shadows stay still, which costs nothing. If a machine stays under 10 frames a second, the player stops the motion and the board stays still.

## Where the files live

The player knows only `/assets/<sha256>.mesh`, with no pack name. The server finds the file by asking which pack names that hash, and serves it with a long-lived cache header. To move the files to other storage, send that path there, and take the mesh files out of the server's required-file check. Nothing else changes. Lean names files only by hash.

If a file is missing or bad, the player keeps the stand-in shape from the `defineMeshFile` command, in that command's colour, and logs one warning. The table stays playable.

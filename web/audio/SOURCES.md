# Where these sounds come from

Everything here was made by `scripts/sound/render.py`. Nothing was downloaded except the SoundFont. No sample pack was used. `scripts/sound/check.py` checks the files by numbers.

## The tools

- **The SoundFont:** MuseScore General SoundFont v0.2.0, under the MIT license. The license and its notices are in `MuseScore_General_License.md`, beside this file. Source: <https://ftp.osuosl.org/pub/musescore/soundfont/MuseScore_General/MuseScore_General.sf2>. It is 215 MB and is not in this repository. Pass it to the script with `--sf`.
- **FluidSynth** plays its notes. **ffmpeg** with LAME writes the MP3 files.
- **The music** uses the trailer's score tool, `scripts/trailer/music.py`: its themes, instruments and mix.

MP3 is the one format that every browser decodes without help. A decoder may leave a little silence at the start of a file. `web/sound.js` measures that and starts after it.

## Short sounds, in `fx/`

**Made with numpy only**, from decaying tones for a knock and shaped noise for paper:
tool, tool-off, tap, place-spot, place-link, refuse, end-turn, page, card-out, dice-rattle, dice-land, dice-hard, coin, quill, stamp-yes, stamp-no, bank, vote-call, fall, talk, offer-in, law-fire, repeal.

**With SoundFont notes:**

| Sound | Instruments |
|---|---|
| place-up | marimba, over numpy |
| your-turn | vibraphone, harp, celesta |
| payday | harp, over numpy coins |
| deal | marimba, over numpy knocks |
| seal, monument | taiko, over numpy |
| law-fail | timpani, pizzicato strings |
| draft-ready | harp |
| rare | tubular bells, glockenspiel, harp, over a numpy rush of air |
| lead, lead-lost | French horn, and for lead also harp, glockenspiel and timpani |
| score-up, score-down | marimba |
| win | trumpets, horns, tuba, strings, timpani, harp |
| lose | strings, double bass, horn, timpani |
| end | harp, strings |
| begin | timpani, horn, harp |

crash and rumble use the trailer's own crash and rumble recipes from `scripts/trailer/music.py`.

## Loops, in `music/`

`tracks.json` holds the exact length of each loop, in seconds. The player uses it to find the join.

| Track | World | Sound |
|---|---|---|
| table | Tutorial Island, and any world with no track of its own | the trailer's theme in F: violin, gut string, strings, flute, horn, frame drum |
| not-catan | Not Catan | the same theme in D Dorian: violin, gut string, accordion, bassoon. The trailer has no Not Catan section, so this one is new. |
| slime | Slime Parliament | the trailer's sagging pizzicato, tuba, bassoon, numpy bubbles and squelches |
| bubble | The AI Bubble | the trailer's glass strings and synth pulse, climbing a half step at a time. It falls back and does not burst. |
| pirate | The Pirate Republic | the trailer's hornpipe: fiddle, accordion, tuba, stomps, numpy creaks |
| strike | Strike the Earth | the trailer's low horns, tuba, taiko, numpy anvil |

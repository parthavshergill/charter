// What the constitution promises a player. This is the only place the words live: edit them here.
// Each `line` is one statement, and `theorem` is the name of the proof behind it, in
// Charter/Constitution.lean. `small` is small print, for a line that is not honest without it.
export const CONSTITUTION = {
  heading: "The Constitution",
  opening: "Rules move things when something happens. Your table can pass rules like that, and these always hold.",
  promises: [
    { n: "I", line: "Nothing comes from nowhere.", theorem: "I_nothing_from_nothing" },
    { n: "II", line: "The game plays no favourites.", theorem: "II_one_law_for_all",
      small: "Going first is still going first, and a tie goes to the earlier seat. A rule can target whoever is ahead." },
    { n: "III", line: "Only a majority can change the rules.", theorem: "III_only_the_majority" },
    { n: "IV", line: "Deals are paid up front.", theorem: "IV_promises_are_paid_up_front" },
    { n: "V", line: "Only you or a rule in force can move what's yours.", theorem: "V_your_money_is_yours" },
    { n: "VI", line: "Every deal ends.", theorem: "VI_every_deal_ends" },
    { n: "VII", line: "A build costs its price, plus what rules add.", theorem: "VII_prices_are_real" },
    { n: "VIII", line: "Nobody can change a roll.", theorem: "VIII_nobody_controls_the_dice",
      small: "This rests on things that are not proved: the server publishes its fingerprint first, it uses your number, it keeps its seed secret until the end, and SHA-256 hides the seed. The server picks the numbers for bots and Claude seats." },
    { n: "IX", line: "Nobody can stall the game.", theorem: "IX_cannot_stall_always_ends",
      small: "The turn timer is the server's job, and it is not proved. A table waits when all its people are away." },
    { n: "X", line: "What you vote on is what runs.", theorem: "X_what_you_vote_on_is_what_runs",
      small: "The rule source is what runs. A description is Claude's reading of it. The preview covers the next turn, and moves made first can change the answer." },
  ],
  notPromised: "Not promised: a fair game or a kind table.",
};

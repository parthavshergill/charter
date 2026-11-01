// What the constitution promises a player. This is the only place the words live: edit them here.
// Each `line` is one statement, and `theorem` is the name of the proof behind it, in
// Charter/Constitution.lean. `small` is small print, for a line that is not honest without it.
export const CONSTITUTION = {
  heading: "The Constitution",
  opening: "Rules move things when something happens. Your table can pass any rule like that, and these always hold.",
  promises: [
    { n: "I", line: "Nothing comes from nowhere.", theorem: "I_nothing_from_nothing" },
    { n: "II", line: "The game plays no favourites.", theorem: "II_one_law_for_all" },
    { n: "III", line: "Only a majority can change the rules.", theorem: "III_only_the_majority" },
    { n: "IV", line: "Deals are paid up front.", theorem: "IV_promises_are_paid_up_front" },
    { n: "V", line: "Only you or a passed rule can move what's yours.", theorem: "V_your_money_is_yours" },
    { n: "VI", line: "Every deal ends.", theorem: "VI_every_deal_ends" },
    { n: "VII", line: "You pay exactly the price shown.", theorem: "VII_prices_are_real" },
    { n: "VIII", line: "Nobody can change a roll.", theorem: "VIII_nobody_controls_the_dice",
      small: "This rests on four things that are not proved: the server publishes its fingerprint first, it uses your number, it keeps its seed secret until the end, and SHA-256 hides the seed." },
    { n: "IX", line: "Nobody can stall the game.", theorem: "IX_cannot_stall_always_ends" },
    { n: "X", line: "What you vote on is what runs.", theorem: "X_what_you_vote_on_is_what_runs",
      small: "The preview covers the next turn. Moves made first can change the answer." },
  ],
  notPromised: "Not promised: a fair game or a kind table.",
};

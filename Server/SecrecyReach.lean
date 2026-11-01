import Server.SecrecyPromise
import Server.Game

/-!
# How far the secrecy promise reaches

`nobody_sees_what_is_hidden` is about `observe`. These two theorems carry it to two things the server
really sends: the preview of a law, and the chronicle's lines for one step. Each says that the function
reads the state only through `observe`, so two states that differ only in what is hidden give the viewer
the same result.

What they do not cover: that the server calls these functions, and that the rest of the view, the scene,
the Claude seats' prompts and the clerk's prompts are built from `observe` too. That is tested, in
`ServerTests.lean`, and the test of the routes is in `scripts/secrecy_check.py`.
-/

namespace CharterServer.SecrecyReach

open Charter CharterServer CharterServer.Secrecy CharterServer.Game

/-- **The preview tells nothing hidden.** Two running states that differ only in what is hidden from the
viewer give it the same preview of any law. -/
theorem previews_hide {G : GameDef} (sec : Secrecy) (you : Option Seat) (s₁ s₂ : State G)
    (hRunning : s₁.phase ≠ .ended) (hd : HiddenDifference sec you s₁ s₂)
    (id : Nat) (L : Law) (names : Nat → String) :
    Preview.seatPreview sec s₁ id L you names = Preview.seatPreview sec s₂ id L you names := by
  have h := (nobody_sees_what_is_hidden sec you s₁ s₂ hRunning).2 hd
  simp only [Preview.seatPreview, h]

/-- **The chronicle tells nothing hidden.** Take two steps, each from a state to the next by an event, in
two games that agree on what this viewer may know of them: names, rules, decisions, and the viewer's own
chronicle so far. If the states before differ only in what is hidden from the viewer, the states after do
too, the game has not ended, and the events look the same to it, then the lines it is told are the same. -/
theorem chronicle_hides {G : GameDef} (g₁ g₂ : Game) (v : Option Seat) (s₁ s₁' s₂ s₂' : State G)
    (e₁ e₂ : Event) (hGame : g₁.publicFor v = g₂.publicFor v)
    (hBefore : s₁.phase ≠ .ended) (hAfter : s₁'.phase ≠ .ended)
    (hd : HiddenDifference g₁.secrecy v s₁ s₂) (hd' : HiddenDifference g₁.secrecy v s₁' s₂')
    (he : observeEvent g₁.secrecy v e₁ = observeEvent g₁.secrecy v e₂) :
    stepLines g₁ v s₁ s₁' e₁ = stepLines g₂ v s₂ s₂' e₂ := by
  have hsec : (g₂.publicFor v).spec.secrecy = g₁.secrecy := by rw [← hGame]; rfl
  have h := (nobody_sees_what_is_hidden _ v s₁ s₂ hBefore).2 hd
  have h' := (nobody_sees_what_is_hidden _ v s₁' s₂' hAfter).2 hd'
  simp only [stepLines, hGame, linesFrom, hsec, h, h', he]

end CharterServer.SecrecyReach

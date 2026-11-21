/-
  The diagonal lemma for strategic voting (Lemma 7 of the draft
  "Cycles, twists and walls"), stated abstractly.

  Setting, seen from one voter i with a fixed preference:
  * `B`   : the voter's possible ballots,
  * `R`   : profiles of the other voters' ballots,
  * `O`   : outcomes,
  * `g`   : the game form, ballot × others' ballots → outcome,
  * `pref x y` : "outcome x is at least as good as y" for this voter.

  Programs are modelled only through what they do:
  * `Env` : the possible inputs (the source codes of the other programs),
  * `M e` : what the strategist outputs on input `e`;
            `none` means it does not halt,
  * `opp e` : what the other programs output on input `e`.

  The only computational assumption is `CanSimulate`: for every way `f`
  of turning the strategist's answer into a counter-move, there is an
  input on which the other programs run the strategist and answer with `f`.
  This uses only core Lean, no Mathlib.
-/

namespace Diagonal

variable {B R O Env : Type}

/-- Ballot `b` is a best reply to the others' ballots `r`. -/
def BestReply (g : B → R → O) (pref : O → O → Prop) (b : B) (r : R) : Prop :=
  ∀ b' : B, pref (g b r) (g b' r)

/-- Ballot `b` is a best reply to everything the others might do. -/
def Dominant (g : B → R → O) (pref : O → O → Prop) (b : B) : Prop :=
  ∀ r : R, BestReply g pref b r

/-- On every input the strategist halts with a best reply to what the
    others actually play. -/
def UniversallyCorrect (g : B → R → O) (pref : O → O → Prop)
    (M : Env → Option B) (opp : Env → Option R) : Prop :=
  ∀ e : Env, ∃ b r, M e = some b ∧ opp e = some r ∧ BestReply g pref b r

/-- The other programs can run the strategist and react to its output. -/
def CanSimulate (M : Env → Option B) (opp : Env → Option R) : Prop :=
  ∀ f : B → R, ∃ e : Env, opp e = (M e).map f

/-- Lemma 7: without a dominant ballot, no strategist is universally correct
    against opponents that can simulate it. -/
theorem lemma7 (g : B → R → O) (pref : O → O → Prop)
    (M : Env → Option B) (opp : Env → Option R)
    (noDom : ¬ ∃ b, Dominant g pref b)
    (sim : CanSimulate M opp) :
    ¬ UniversallyCorrect g pref M opp := by
  intro hM
  -- Every ballot has a profile that refutes it (this is where "no dominant
  -- ballot" is used).
  have refute : ∀ b : B, ∃ r : R, ¬ BestReply g pref b r := by
    intro b
    apply Classical.byContradiction
    intro h
    apply noDom
    exact ⟨b, by intro r; exact Classical.byContradiction (fun hr => h ⟨r, hr⟩)⟩
  -- The diagonal: answer each ballot with a profile refuting it.
  let f : B → R := fun b => Classical.choose (refute b)
  obtain ⟨e, he⟩ := sim f
  obtain ⟨b, r, hb, hr, hbest⟩ := hM e
  rw [hb, hr] at he
  -- he : some r = Option.map f (some b), which reduces to some (f b)
  have hrf : r = f b := Option.some.inj he
  rw [hrf] at hbest
  exact Classical.choose_spec (refute b) hbest

end Diagonal

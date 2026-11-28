/-
  The theorem for three outcomes of *The rational diagonal on totally tight
  game forms* (`notes/rational-diagonal-totally-tight.md`, Section 7), by
  hand, without the summary search.

  Setting as in `TwoPlayer.lean` and `ThreeOutcomes.lean`: rows are player 1's
  strategies, columns player 2's, strict preferences are injective utilities,
  and the sets of rows and columns need not be finite.

  * `IsTotallyTight`: every 2 × 2 subform has a constant row or column, the
    note's description of a tight 2 × 2 form.
  * `Recomb`, the property (R): for any two cells (r, s₀) and (r₀, s) there is
    a row r′ with the same outcomes in columns s₀ and s, or a column s′ with
    the same outcomes in rows r and r₀. Totally tight forms have it
    (`recomb_of_totallyTight`), and it passes to the transpose
    (`recomb_transpose`).
  * `F2`, `F3`: the facts (F2) and (F3) of the note, (F3) from (R). Fact (F1)
    enters through the hypotheses of `ThreeOutcomes.works_rev`, which asks
    that the opponent does not force the bottom outcome.
  * `chain` (the chain lemma): with outcomes a, c, e, if player 1 does not
    force a and player 2 does not force c, one of the four configurations
    (1, (a, e, c), reverse), (2, (c, a, e), rotation), (1, (a, c, e),
    rotation), (2, (c, e, a), reverse) works, each step using the failure of
    the one before. The configurations are `ThreeOutcomes.works_rev` and
    `ThreeOutcomes.works_rot`, read on the transpose for the other player.
  * `three_outcomes`: every non-dictatorial form with (R) and three outcomes,
    all occurring, admits a rational diagonal for some player;
    `three_outcomes_tt` for totally tight forms.

  Not here: that games of perfect information have (R), which needs their
  normal forms; the reduction to seven outcomes and the searches for more
  outcomes (Proposition 5′).
-/

module

public import Mathlib
public import ThreeOutcomes

@[expose] public section

namespace TotallyTight

open NonTight TwoPlayer ThreeOutcomes

variable {A B X : Type}

/-- Every 2 × 2 subform has a constant row or column. -/
def IsTotallyTight (g : A → B → X) : Prop :=
  ∀ r r₀ s₀ s, g r s₀ = g r s ∨ g r₀ s₀ = g r₀ s ∨ g r s₀ = g r₀ s₀ ∨ g r s = g r₀ s

/-- The recombination property (R). -/
def Recomb (g : A → B → X) : Prop :=
  ∀ r s₀ r₀ s, (∃ r', g r' s₀ = g r s₀ ∧ g r' s = g r₀ s) ∨
    (∃ s', g r s' = g r s₀ ∧ g r₀ s' = g r₀ s)

theorem recomb_of_totallyTight {g : A → B → X} (h : IsTotallyTight g) : Recomb g := by
  intro r s₀ r₀ s
  rcases h r r₀ s₀ s with e | e | e | e
  · exact Or.inr ⟨s, e.symm, rfl⟩
  · exact Or.inr ⟨s₀, rfl, e⟩
  · exact Or.inl ⟨r₀, e.symm, rfl⟩
  · exact Or.inl ⟨r, rfl, e⟩

theorem recomb_transpose {g : A → B → X} (h : Recomb g) : Recomb (transpose g) := by
  intro b a₀ b₀ a
  rcases h a b₀ a₀ b with ⟨r', h1, h2⟩ | ⟨s', h1, h2⟩
  · exact Or.inr ⟨r', h2, h1⟩
  · exact Or.inl ⟨s', h2, h1⟩

/-- **(F2).** Every row inside {v, w} holding w reaches v from w, or every
    column inside {u, w} holding w leaves w. -/
lemma F2 {g : A → B → X} {u v w : X} (huv : u ≠ v) (hvw : v ≠ w)
    (hv : ∃ r s, g r s = v) :
    (∀ r, (∀ s, g r s = v ∨ g r s = w) → (∃ s, g r s = w) → ∃ s, g r s = w ∧ ∃ r', g r' s = v) ∨
    (∀ s, (∀ r, g r s = u ∨ g r s = w) → (∃ r, g r s = w) →
      ∃ r, g r s = w ∧ ∃ s', g r s' ≠ w) := by
  by_contra hno
  push Not at hno
  obtain ⟨⟨r, hrin, -, hr⟩, ⟨s, hsin, -, hs⟩⟩ := hno
  have hc : g r s = w := by
    rcases hrin s with e | e
    · rcases hsin r with e' | e'
      · exact absurd (e'.symm.trans e) huv
      · exact absurd (e.symm.trans e') hvw
    · exact e
  obtain ⟨r1, s1, h1⟩ := hv
  exact hr s1 (hs r hc s1) r1 h1

/-- **(F3) from (R).** Every row holding w reaches v from w, or every column
    holding v reaches w from v. -/
lemma F3 {g : A → B → X} (hR : Recomb g) {v w : X} :
    (∀ r, (∃ s, g r s = w) → ∃ s, g r s = w ∧ ∃ r', g r' s = v) ∨
    (∀ s, (∃ r, g r s = v) → ∃ r, g r s = v ∧ ∃ s', g r s' = w) := by
  by_contra hno
  push Not at hno
  obtain ⟨⟨r, ⟨s1, hs1⟩, hr⟩, ⟨s, ⟨r1, hr1⟩, hs⟩⟩ := hno
  rcases hR r s1 r1 s with ⟨r', h1, h2⟩ | ⟨s', h1, h2⟩
  · exact hs r' (h2.trans hr1) s1 (h1.trans hs1)
  · exact hr s' (h1.trans hs1) r1 (h2.trans hr1)

variable [DecidableEq X]

/-- **The chain lemma.** With three outcomes a, c, e, if player 1 does not force
    a and player 2 does not force c, one of four configurations works. -/
theorem chain {g : A → B → X} (hR : Recomb g) {a c e : X} (hac : a ≠ c) (hae : a ≠ e)
    (hce : c ≠ e) (hcov : ∀ x, x = a ∨ x = c ∨ x = e) (ha : ∃ r s, g r s = a)
    (hc : ∃ r s, g r s = c) (h1a : ¬ ∃ r, ∀ s, g r s = a) (h2c : ¬ ∃ s, ∀ r, g r s = c) :
    RationalDiagonal1 g ∨ RationalDiagonal2 g := by
  have cov1 : ∀ x, x = a ∨ x = e ∨ x = c := fun x => by
    rcases hcov x with h | h | h <;> tauto
  have cov3 : ∀ x, x = c ∨ x = a ∨ x = e := fun x => by
    rcases hcov x with h | h | h <;> tauto
  have cov4 : ∀ x, x = c ∨ x = e ∨ x = a := fun x => by
    rcases hcov x with h | h | h <;> tauto
  -- 1. (1, (a, e, c), reverse)
  by_cases h1 : ∀ r, (∀ s, g r s = a ∨ g r s = e) → (∃ s, g r s = e) →
      ∃ s, g r s = e ∧ ∃ r', g r' s = a
  · exact Or.inl (works_rev hae hac hce.symm cov1 h2c h1a h1)
  -- 2. (2, (c, a, e), rotation), with (F2)
  have f2 := (F2 hac.symm hae ha).resolve_left h1
  by_cases h2 : ∀ s, (∃ r, g r s = a) → ∃ r, g r s = a ∧ ∃ s', g r s' = c
  · exact Or.inr (works_rot hac hae hce hcov h2c h2 f2)
  -- 3. (1, (a, c, e), rotation), with (F3)
  have f3 := (F3 hR (v := a) (w := c)).resolve_right h2
  by_cases h3 : ∀ r, (∀ s, g r s = a ∨ g r s = e) → (∃ s, g r s = e) →
      ∃ s, g r s = e ∧ ∃ r', g r' s ≠ e
  · exact Or.inl ((rd2_iff (transpose g)).mp
      (works_rot (g := transpose g) hac.symm hce hae cov3 h1a f3 h3))
  -- 4. (2, (c, e, a), reverse), with (F2) on the transpose
  obtain ⟨r0, s0, h0⟩ := hc
  have f4 := (F2 (g := transpose g) hac hce ⟨s0, r0, h0⟩).resolve_right h3
  exact Or.inr ((rd2_iff g).mpr
    (works_rev (g := transpose g) hce hac.symm hae.symm cov4 h1a h2c f4))

/-- **The theorem for three outcomes.** Every non-dictatorial form with (R) and
    three outcomes, all occurring, admits a rational diagonal for some player. -/
theorem three_outcomes {g : A → B → X} (hR : Recomb g) {a b c : X} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hcov : ∀ x, x = a ∨ x = b ∨ x = c) (honto : ∀ x, ∃ r s, g r s = x)
    (hnd1 : ¬ ∀ x, ∃ r, ∀ s, g r s = x) (hnd2 : ¬ ∀ x, ∃ s, ∀ r, g r s = x) :
    RationalDiagonal1 g ∨ RationalDiagonal2 g := by
  have others : ∀ t : X, ∃ u v : X, t ≠ u ∧ t ≠ v ∧ u ≠ v ∧ ∀ x, x = t ∨ x = u ∨ x = v := by
    intro t
    rcases hcov t with rfl | rfl | rfl
    · exact ⟨b, c, hab, hac, hbc, hcov⟩
    · exact ⟨a, c, hab.symm, hbc, hac, fun x => by rcases hcov x with e | e | e <;> tauto⟩
    · exact ⟨a, b, hac.symm, hbc.symm, hab, fun x => by rcases hcov x with e | e | e <;> tauto⟩
  push Not at hnd1
  obtain ⟨t, ht⟩ := hnd1
  have h1t : ¬ ∃ r, ∀ s, g r s = t := by push Not; exact ht
  obtain ⟨u, v, htu, htv, huv, hc⟩ := others t
  have cov' : ∀ x, x = t ∨ x = v ∨ x = u := fun x => by
    rcases hc x with e | e | e <;> tauto
  by_cases hu : ∃ s, ∀ r, g r s = u
  · by_cases hv : ∃ s, ∀ r, g r s = v
    · -- player 2 forces u and v, so player 1 forces nothing and player 2 not t
      obtain ⟨su, hsu⟩ := hu
      obtain ⟨sv, hsv⟩ := hv
      have h1 : ∀ y, ¬ ∃ r, ∀ s, g r s = y := by
        rintro y ⟨r, hr⟩
        exact huv ((hsu r).symm.trans ((hr su).trans ((hr sv).symm.trans (hsv r))))
      have h2t : ¬ ∃ s, ∀ r, g r s = t := by
        rintro hts
        apply hnd2
        intro x
        rcases hc x with rfl | rfl | rfl
        · exact hts
        · exact ⟨su, hsu⟩
        · exact ⟨sv, hsv⟩
      rcases chain (g := transpose g) (recomb_transpose hR) htu htv huv hc
          (by obtain ⟨r, s, h⟩ := honto t; exact ⟨s, r, h⟩)
          (by obtain ⟨r, s, h⟩ := honto u; exact ⟨s, r, h⟩) h2t (h1 u) with h | h
      · exact Or.inr ((rd2_iff g).mpr h)
      · exact Or.inl ((rd2_iff (transpose g)).mp h)
    · exact chain hR htv htu huv.symm cov' (honto t) (honto v) h1t hv
  · exact chain hR htu htv huv hc (honto t) (honto u) h1t hu

/-- **Totally tight forms with three outcomes.** -/
theorem three_outcomes_tt {g : A → B → X} (hT : IsTotallyTight g) {a b c : X} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (hcov : ∀ x, x = a ∨ x = b ∨ x = c)
    (honto : ∀ x, ∃ r s, g r s = x) (hnd1 : ¬ ∀ x, ∃ r, ∀ s, g r s = x)
    (hnd2 : ¬ ∀ x, ∃ s, ∀ r, g r s = x) : RationalDiagonal1 g ∨ RationalDiagonal2 g :=
  three_outcomes (recomb_of_totallyTight hT) hab hac hbc hcov honto hnd1 hnd2

end TotallyTight

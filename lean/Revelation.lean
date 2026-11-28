/-
  Propositions 3 and 4 of *What a Ballot Reveals*
  (`notes/strategic-information/revelation.md`, Sections 3 and 4).

  Proposition 3, certainty reveals least. A method chooses a single winner
  from the ballots, without chance; the voter's belief gives probabilities
  `p j` to k possibilities for the other ballots, and `w j b` is the winner in
  possibility j when the voter casts b. The lottery of b is `lot p w b`.
  * `menu_card`: the menu has at most m^k different lotteries, since a
    lottery is determined by the k winners.
  * `certainty`: under certainty the lotteries are sure winners `w b`. A voter
    with a unique best winner (`BestUnique`) chooses it. If the ballot reveals
    the comparison of i and j (`Reveals`: two voters with the same unique best
    winner agree on i against j), then every attainable winner is i or j: a
    third candidate c could be the favourite of voters on both sides.

  Proposition 4, the theorem of Gibbard and Satterthwaite. A method g gives a
  winner for every profile of ballots, and φ fills in a ballot from a
  preference. Preferences are orderings in Gibbard's sense (`Arrow.IsOrdering`,
  ties allowed), as in `Gibbard73.lean`.
  * `prop4`: if φ P is a dominant ballot for every voter at every ordering P,
    whatever the other ballots are, and the composite `fillComp g φ` reaches
    three different winners, then on the ballots filled in by φ the method is
    a dictatorship: some voter can force every winner that filled ballots can
    reach. The proof is the revelation principle. The composite, on its range
    (`Composition.GameForm.ofRange`), is straightforward: an ordering of the
    reachable winners lifts to an ordering of all candidates with the others
    at the bottom (`lift`), and reporting the lifted ordering is dominant
    since its filled ballot is. Gibbard's theorem (`Gibbard73.gibbard`) gives
    the dictator.

  Not here: Propositions 1 and 2 (menus as polytopes, revealed comparisons as
  edges), and Proposition 4 for strict rankings only, which needs the
  theorem of Gibbard and Satterthwaite for strict preferences.
-/

module

public import Mathlib
public import Composition

@[expose] public section

open Finset

namespace Revelation

/-! ### Proposition 3 -/

section Menu

variable {Bal X : Type} [Fintype X] [DecidableEq X] {k : ℕ}

/-- The lottery of a ballot: the probability of each candidate, over the k
    possibilities for the other ballots. -/
def lot (p : Fin k → ℝ) (w : Fin k → Bal → X) (b : Bal) (x : X) : ℝ :=
  ∑ j, if w j b = x then p j else 0

open Classical in
/-- **The menu is small.** At most m^k different lotteries. -/
theorem menu_card (p : Fin k → ℝ) (w : Fin k → Bal → X) (B : Finset Bal) :
    (B.image (lot p w)).card ≤ Fintype.card X ^ k := by
  have e : B.image (lot p w) =
      (B.image fun b j => w j b).image (fun τ x => ∑ j, if τ j = x then p j else 0) := by
    rw [Finset.image_image]
    rfl
  rw [e]
  calc _ ≤ (B.image fun b j => w j b).card := card_image_le
    _ ≤ Fintype.card (Fin k → X) := card_le_univ _
    _ = Fintype.card X ^ k := by simp

/-- Under certainty: x is attainable and better for the voter than every
    other attainable winner. -/
def BestUnique (u : X → ℝ) (w : Bal → X) (x : X) : Prop :=
  (∃ b, w b = x) ∧ ∀ b, w b ≠ x → u (w b) < u x

/-- The ballot reveals the comparison of i and j: two voters with the same
    unique best winner agree on whether they prefer i to j. -/
def Reveals (w : Bal → X) (i j : X) : Prop :=
  ∀ (u v : X → ℝ) x, BestUnique u w x → BestUnique v w x → (u j < u i ↔ v j < v i)

omit [Fintype X] in
/-- **Certainty reveals least.** If the ballot reveals the comparison of i and
    j, only i and j can be made to win. -/
theorem certainty (w : Bal → X) {i j : X} (hij : i ≠ j) (h : Reveals w i j) (b : Bal) :
    w b = i ∨ w b = j := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨hci, hcj⟩ := hc
  generalize hcdef : w b = c at hci hcj
  let u : X → ℝ := fun y => if y = c then 2 else if y = i then 1 else 0
  let v : X → ℝ := fun y => if y = c then 2 else if y = j then 1 else 0
  have hu : BestUnique u w c := ⟨⟨b, hcdef⟩, fun b' hb' => by
    simp only [u]
    split_ifs <;> first | (exfalso; tauto) | norm_num⟩
  have hv : BestUnique v w c := ⟨⟨b, hcdef⟩, fun b' hb' => by
    simp only [v]
    split_ifs <;> first | (exfalso; tauto) | norm_num⟩
  have := h u v c hu hv
  simp [u, v, Ne.symm hci, Ne.symm hcj, Ne.symm hij, hij] at this
  norm_num at this

end Menu

/-! ### Proposition 4 -/

section GS

open Arrow Gibbard73 Composition

variable {X I Bal : Type} [DecidableEq X] [DecidableEq I]

/-- Orderings in Gibbard's sense. -/
abbrev Ord (X : Type) := {P : Rel X // IsOrdering P}

/-- The method composed with the way of filling in the ballot. -/
def fillComp (g : (I → Bal) → X) (φ : Rel X → Bal) : (I → Ord X) → X :=
  fun Q => g fun i => φ (Q i).1

open Classical in
/-- An ordering of the reachable winners, extended to all candidates with the
    unreachable ones at the bottom. -/
noncomputable def lift (h : (I → Ord X) → X) (P : Rel (Range h)) : Rel X := fun x y =>
  if hx : ∃ s, h s = x then (if hy : ∃ s, h s = y then P ⟨x, hx⟩ ⟨y, hy⟩ else true) else false

omit [DecidableEq X] [DecidableEq I] in
lemma lift_ord (h : (I → Ord X) → X) {P : Rel (Range h)} (hP : IsOrdering P) :
    IsOrdering (lift h P) where
  asymm := by
    intro x y hxy
    by_cases hx : ∃ s, h s = x <;> by_cases hy : ∃ s, h s = y <;>
      simp [lift, hx, hy] at hxy ⊢
    exact hP.asymm _ _ hxy
  negTrans := by
    intro x y z hxz
    by_cases hx : ∃ s, h s = x <;> by_cases hy : ∃ s, h s = y <;> by_cases hz : ∃ s, h s = z <;>
      simp [lift, hx, hy, hz] at hxz ⊢
    exact hP.negTrans _ _ _ hxz

omit [DecidableEq X] [DecidableEq I] in
lemma lift_range (h : (I → Ord X) → X) (P : Rel (Range h)) (Q Q' : I → Ord X) :
    lift h P (h Q) (h Q') = P (toRange h Q) (toRange h Q') := by
  simp [lift, toRange]

/-- **Proposition 4.** If filling in the ballot from the preference is always
    a dominant ballot, and filled ballots can make three different winners,
    then on filled ballots the method is a dictatorship. -/
theorem prop4 (g : (I → Bal) → X) (allX : List X) (hallX : ∀ x, x ∈ allX) (allI : List I)
    (hallI : ∀ i, i ∈ allI) (φ : Rel X → Bal)
    (hφ : ∀ P : Rel X, IsOrdering P → ∀ k, Dominant g P k (φ P))
    (Q₁ Q₂ Q₃ : I → Ord X) (h₁₂ : fillComp g φ Q₁ ≠ fillComp g φ Q₂)
    (h₁₃ : fillComp g φ Q₁ ≠ fillComp g φ Q₃) (h₂₃ : fillComp g φ Q₂ ≠ fillComp g φ Q₃) :
    ∃ k, ∀ Q₀ : I → Ord X, ∃ t : Ord X, ∀ Q, Q k = t → fillComp g φ Q = fillComp g φ Q₀ := by
  let Gf := GameForm.ofRange (fillComp g φ) allX hallX allI hallI Q₁ Q₂ Q₃ h₁₂ h₁₃ h₂₃
  have hs : Straightforward Gf.g := by
    intro P hP k
    refine ⟨⟨lift (fillComp g φ) P, lift_ord _ hP⟩, fun Q => ?_⟩
    have hd := hφ (lift (fillComp g φ) P) (lift_ord _ hP) k (fun i => φ (Q i).1)
    have e : upd (fun i => φ (Q i).1) k (φ (lift (fillComp g φ) P)) =
        fun i => φ ((upd Q k ⟨lift (fillComp g φ) P, lift_ord _ hP⟩) i).1 := by
      funext i
      unfold upd
      split_ifs <;> rfl
    rw [e] at hd
    show P (toRange (fillComp g φ) Q)
      (toRange (fillComp g φ) (upd Q k ⟨lift (fillComp g φ) P, lift_ord _ hP⟩)) = false
    rw [← lift_range (fillComp g φ) P Q (upd Q k ⟨lift (fillComp g φ) P, lift_ord _ hP⟩)]
    exact hd
  obtain ⟨k, hk⟩ := gibbard Gf hs
  exact ⟨k, (isDictator_toRange (fillComp g φ) k).mp hk⟩

end GS

end Revelation

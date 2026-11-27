/-
  Proposition 5″ of *Walls and Strategy* (working note *A tight form without
  a rational diagonal*, Section 1): an explicit 6 × 6 two-player game form with
  three outcomes that is tight and not dictatorial, and in which, under every
  pair of strict preferences, each player has a strict Nash strategy. So
  neither player admits a rational diagonal (`no_diagonal1`, `no_diagonal2`).

  The definitions are those of `NonTight.lean` (best replies, strict
  preferences as injective utilities, tightness, `RationalDiagonal1`), with
  strict Nash strategies and the common veto from `TwoPlayer.lean`, so this
  is the counterpart of Proposition 5 there: on forms that are not tight the
  diagonal always exists, on this tight form it never does.

  Method. A strict Nash strategy of player 1 is a row that is a best reply to
  every best reply of player 2 (`StrictNash1`); a rational diagonal exists
  exactly when there is none (`not_rd1_iff`). Best replies depend only on the
  order of the utilities, and every injective utility on three outcomes has
  the order of its rank, a utility with values 0, 1, 2 (`rank3`). This reduces
  the claim for all utilities to the 36 pairs of rankings, which `decide`
  checks (`core_form`, and `core_transpose` for player 2) with instances
  for the pieces of the statement. The common veto c,
  a constant row and a constant column, gives tightness for any form
  (`tight_of_common_veto`).
-/

module

public import Mathlib
public import NonTight
public import TwoPlayer

@[expose] public section

namespace TightCounterexample

open NonTight TwoPlayer

/-! ### Utilities on three outcomes up to order -/

/-- The utility with values p, q, r on the outcomes 0, 1, 2. -/
def tri (p q r : Nat) : Fin 3 → Nat
  | ⟨0, _⟩ => p
  | ⟨1, _⟩ => q
  | _ => r

/-- The rank of x under u: the number of outcomes worse than x. -/
def rank3 (u : Fin 3 → Nat) (x : Fin 3) : Nat :=
  (if u 0 < u x then 1 else 0) + (if u 1 < u x then 1 else 0) + (if u 2 < u x then 1 else 0)

theorem fin3_forall {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ x, P x := by
  intro x
  fin_cases x
  · exact h0
  · exact h1
  · exact h2

theorem rank3_lt (u : Fin 3 → Nat) : ∀ x, rank3 u x < 3 := by
  refine fin3_forall ?_ ?_ ?_ <;> (unfold rank3; split_ifs <;> omega)

theorem rank3_iff (u : Fin 3 → Nat) (hu : Injective u) :
    ∀ x y, u x ≤ u y ↔ rank3 u x ≤ rank3 u y := by
  have h01 : u 0 ≠ u 1 := fun h => absurd (hu 0 1 h) (by decide)
  have h02 : u 0 ≠ u 2 := fun h => absurd (hu 0 2 h) (by decide)
  have h12 : u 1 ≠ u 2 := fun h => absurd (hu 1 2 h) (by decide)
  refine fin3_forall ?_ ?_ ?_ <;> refine fin3_forall ?_ ?_ ?_ <;>
    (unfold rank3; split_ifs <;> constructor <;> intro <;> omega)

theorem rank3_eq_tri (u : Fin 3 → Nat) : rank3 u = tri (rank3 u 0) (rank3 u 1) (rank3 u 2) := by
  funext x
  revert x
  exact fin3_forall rfl rfl rfl

/-- The six rankings of three outcomes, as the utilities (p, q, r) of the
    outcomes 0, 1, 2. -/
def rankings : List (Nat × Nat × Nat) :=
  [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]

/-- The utility of a ranking. -/
def util (P : Nat × Nat × Nat) : Fin 3 → Nat := tri P.1 P.2.1 P.2.2

theorem mem_rankings : ∀ p < 3, ∀ q < 3, ∀ r < 3, p ≠ q → p ≠ r → q ≠ r →
    (p, q, r) ∈ rankings := by
  intro p hp q hq r hr h₁ h₂ h₃
  interval_cases p <;> interval_cases q <;> interval_cases r <;>
    first | (exfalso; omega) | decide

/-- Every strict preference on three outcomes has the order of one of the six
    rankings. -/
theorem exists_ranking (u : Fin 3 → Nat) (hu : Injective u) :
    ∃ P ∈ rankings, ∀ x y, u x ≤ u y ↔ util P x ≤ util P y := by
  have hi := rank3_iff u hu
  have ne : ∀ x y : Fin 3, x ≠ y → rank3 u x ≠ rank3 u y := fun x y hxy h =>
    hxy (hu x y (le_antisymm ((hi x y).mpr h.le) ((hi y x).mpr h.ge)))
  refine ⟨(rank3 u 0, rank3 u 1, rank3 u 2),
    mem_rankings _ (rank3_lt u 0) _ (rank3_lt u 1) _ (rank3_lt u 2)
      (ne 0 1 (by decide)) (ne 0 2 (by decide)) (ne 1 2 (by decide)), ?_⟩
  show ∀ x y, u x ≤ u y ↔ tri (rank3 u 0) (rank3 u 1) (rank3 u 2) x ≤
    tri (rank3 u 0) (rank3 u 1) (rank3 u 2) y
  rw [← rank3_eq_tri u]
  exact hi

/-! ### Decidability on finite forms

Instances for the pieces, so that `decide` never has to assemble one instance
for a long statement. -/

section Decidable

variable {m n : Nat} {X : Type}

instance (g : Fin m → Fin n → X) (u : X → Nat) (a : Fin m) (b : Fin n) :
    Decidable (BR1 g u a b) :=
  inferInstanceAs (Decidable (∀ a' : Fin m, u (g a' b) ≤ u (g a b)))

instance (g : Fin m → Fin n → X) (v : X → Nat) (a : Fin m) (b : Fin n) :
    Decidable (BR2 g v a b) :=
  inferInstanceAs (Decidable (∀ b' : Fin n, v (g a b') ≤ v (g a b)))

instance (g : Fin m → Fin n → X) (u v : X → Nat) (a : Fin m) :
    Decidable (StrictNash1 g u v a) :=
  inferInstanceAs (Decidable (∀ b : Fin n, BR2 g v a b → BR1 g u a b))

end Decidable

/-- For every pair of rankings, player 1 has a strict Nash strategy. -/
def Core {m n : Nat} (g : Fin m → Fin n → Fin 3) : Prop :=
  ∀ P ∈ rankings, ∀ Q ∈ rankings, ∃ a, StrictNash1 g (util P) (util Q) a

instance {m n : Nat} (g : Fin m → Fin n → Fin 3) : Decidable (Core g) :=
  inferInstanceAs
    (Decidable (∀ P ∈ rankings, ∀ Q ∈ rankings, ∃ a, StrictNash1 g (util P) (util Q) a))

/-- From the 36 pairs of rankings to all strict preferences. -/
theorem no_diagonal_of_core {m n : Nat} (g : Fin m → Fin n → Fin 3) (hc : Core g) :
    ¬ RationalDiagonal1 g := by
  rw [not_rd1_iff]
  intro u v hu hv
  obtain ⟨P, hP, hu'⟩ := exists_ranking u hu
  obtain ⟨Q, hQ, hv'⟩ := exists_ranking v hv
  obtain ⟨a, ha⟩ := hc P hP Q hQ
  exact ⟨a, fun b hb => (br1_congr g hu' a b).mpr (ha b ((br2_congr g hv' a b).mp hb))⟩

/-! ### The form -/

/-- The outcomes a, b, c. -/
abbrev oa : Fin 3 := 0
abbrev ob : Fin 3 := 1
abbrev oc : Fin 3 := 2

/-- Rows are player 1's strategies r0, …, r5, columns player 2's s0, …, s5. -/
def form : Fin 6 → Fin 6 → Fin 3 :=
  ![![oc, oc, oc, oc, oc, oc],
    ![oc, ob, oa, ob, oa, oa],
    ![oc, ob, oc, ob, ob, ob],
    ![oc, ob, oa, oc, oc, oa],
    ![oc, oc, oa, oa, oa, oa],
    ![oc, ob, oa, ob, oc, ob]]

/-- The form seen from player 2: its strategies as rows. -/
def formT : Fin 6 → Fin 6 → Fin 3 := fun s r => form r s

/-- All three outcomes occur. -/
theorem form_onto : ∀ x : Fin 3, ∃ r s, form r s = x := by decide +kernel

/-- Tight, by the common veto c in row r0 and column s0. -/
theorem form_tight : Tight form :=
  tight_of_common_veto form oc 0 (by decide +kernel) 0 (by decide +kernel)

/-- Not dictatorial: neither player can force every outcome. -/
theorem form_not_dictatorial :
    ¬ (∀ x, ∃ r, ∀ s, form r s = x) ∧ ¬ (∀ x, ∃ s, ∀ r, form r s = x) := by
  decide +kernel

theorem core_form : Core form := by decide +kernel

theorem core_transpose : Core formT := by decide +kernel

/-- Proposition 5″, player 1: no rational diagonal. -/
theorem no_diagonal1 : ¬ RationalDiagonal1 form := no_diagonal_of_core form core_form

/-- Proposition 5″, player 2: no rational diagonal. -/
theorem no_diagonal2 : ¬ RationalDiagonal2 form := fun h =>
  no_diagonal_of_core formT core_transpose ((rd2_iff form).mp h)

end TightCounterexample

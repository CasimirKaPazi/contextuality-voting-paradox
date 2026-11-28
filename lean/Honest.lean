/-
  Proposition 2 of *The Honest Axis* (`notes/strategic-information/honest.md`,
  Section 2): with scores 0 to k and n honest voters, the winner of score
  voting has a sum of normalised utilities within n/k of the largest.

  Voters `V`, candidates `X`; `ν v x` is voter v's normalised utility of x
  (worst at 0, best at 1), `s v x` the score v gives x.
  * `honest_round`: the honest score, k ν rounded to a whole score, is
    within one half of k ν.
  * `prop2`: if every score is within one half of k ν and w has the largest
    total score, then for every candidate y the sum of ν for w is at least
    the sum for y minus n/k. Each total, divided by k, is within n/(2k) of the
    sum of ν.

  Not here: Propositions 1, 3 and 4.
-/

module

public import Mathlib

@[expose] public section

open Finset

namespace Honest

/-- The honest score is within one half of k ν. -/
lemma honest_round (k ν : ℝ) : |(round (k * ν) : ℝ) - k * ν| ≤ 1 / 2 := by
  rw [abs_sub_comm]
  exact abs_sub_round _

variable {V X : Type} [Fintype V]

/-- **Proposition 2.** The winner of score voting with honest scores 0 to k
    has a sum of normalised utilities within n/k of the largest. -/
theorem prop2 (k : ℕ) (hk : 0 < k) (ν s : V → X → ℝ) (hs : ∀ v x, |s v x - k * ν v x| ≤ 1 / 2)
    (w : X) (hw : ∀ y, ∑ v, s v y ≤ ∑ v, s v w) (y : X) :
    ∑ v, ν v y - (Fintype.card V : ℝ) / k ≤ ∑ v, ν v w := by
  have hA : ∀ x, |∑ v, s v x - k * ∑ v, ν v x| ≤ (Fintype.card V : ℝ) / 2 := fun x =>
    calc |∑ v, s v x - k * ∑ v, ν v x| = |∑ v, (s v x - k * ν v x)| := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ ≤ ∑ v, |s v x - k * ν v x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v : V, (1 / 2 : ℝ) := Finset.sum_le_sum fun v _ => hs v x
      _ = (Fintype.card V : ℝ) / 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  obtain ⟨hw1, hw2⟩ := abs_le.mp (hA w)
  obtain ⟨hy1, hy2⟩ := abs_le.mp (hA y)
  have hwy := hw y
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkn : (k : ℝ) * ((Fintype.card V : ℝ) / k) = Fintype.card V := by
    field_simp [hkpos.ne']
  have key : (k : ℝ) * (∑ v, ν v y - (Fintype.card V : ℝ) / k) ≤ k * ∑ v, ν v w := by
    rw [mul_sub, hkn]
    linarith
  exact le_of_mul_le_mul_left key hkpos

end Honest

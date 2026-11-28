/-
  Propositions 1 and 4 of *Intensities and the Utilitarian Target*
  (`notes/strategic-information/intensity.md`, Sections 1 and 4).

  * `prop1` (scale is never revealed): a ballot b leads to a lottery `P b`
    over the candidates, with probabilities adding up to one. Its value for
    utilities u is `value u P b`, and b is a best reply when no ballot has a
    larger value (`IsBest`). The best replies for u and for λu + c, λ > 0,
    are the same, since every value becomes λ · value + c.
  * `prop4` (certifying the leader leaves no room for intensities): in the
    frame of `LeaderRank.lean`, a strategic count that certifies the leader
    and, with the size of the electorate, has rank at most m (as for a count
    of totals) gives the same column to two types that prefer the same
    candidates to the leader. By `LeaderRank.prop3_rowspace` every row is a
    combination of the leader's margins and the size. So the ballot of a type
    depends on its utilities only through the set of candidates it prefers
    to the leader, and reveals no intensity. Read the other way: a ballot
    that distinguishes two such types does not certify the leader.

  Not here: Propositions 2 and 3 (totals in the linear regime, corners and
  roundness).
-/

module

public import Mathlib
public import LeaderRank

@[expose] public section

open Finset

namespace Intensity

/-! ### Proposition 1 -/

section Scale

variable {Bal X : Type} [Fintype X]

/-- The expected utility of a ballot. -/
def value (u : X → ℝ) (P : Bal → X → ℝ) (b : Bal) : ℝ := ∑ x, u x * P b x

/-- b is a best reply: no ballot has a larger value. -/
def IsBest (u : X → ℝ) (P : Bal → X → ℝ) (b : Bal) : Prop := ∀ b', value u P b' ≤ value u P b

lemma value_affine (u : X → ℝ) (P : Bal → X → ℝ) (hP : ∀ b, ∑ x, P b x = 1) (l c : ℝ) (b : Bal) :
    value (fun x => l * u x + c) P b = l * value u P b + c := by
  simp only [value, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, hP, mul_one]

/-- **Proposition 1.** Best replies are the same for u and for λu + c. -/
theorem prop1 (u : X → ℝ) (P : Bal → X → ℝ) (hP : ∀ b, ∑ x, P b x = 1) {l : ℝ} (hl : 0 < l)
    (c : ℝ) (b : Bal) : IsBest (fun x => l * u x + c) P b ↔ IsBest u P b := by
  unfold IsBest
  simp only [value_affine u P hP]
  constructor
  · intro h b'
    exact le_of_mul_le_mul_left (by linarith [h b']) hl
  · intro h b'
    have := mul_le_mul_of_nonneg_left (h b') hl.le
    linarith

end Scale

/-! ### Proposition 4 -/

section Leader

open StrategicCount Certification LeaderRank

variable {m : ℕ} {T ι : Type*} [Fintype T] [Fintype ι] [DecidableEq ι] [DecidableEq T]
  (ρ : T → Equiv.Perm (Fin m))

/-- **Proposition 4.** A count that certifies the leader and has, with the
    size, rank at most m gives the same column to two types that prefer the
    same candidates to the leader. -/
theorem prop4 (hρ : Function.Surjective ρ) (M : Matrix ι T ℤ) (a : Fin m)
    (hC : Certifies M (fun (e : {x // x ≠ a}) t => sgn (ρ t) a e))
    (hr : (qM (withSize M)).rank ≤ m) {t t' : T}
    (hS : ∀ x, x ≠ a → (ρ t a < ρ t x ↔ ρ t' a < ρ t' x)) (i : ι) : M i t = M i t' := by
  have hmem : (qM (withSize M)).row (some i) ∈
      Submodule.span ℚ (Set.range (leaderRow ρ a)) := by
    rw [← prop3_rowspace ρ hρ M a hC hr]
    exact Submodule.subset_span ⟨some i, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hmem
  have key : ∀ j, leaderRow ρ a j t = leaderRow ρ a j t' := by
    intro j
    cases j with
    | none => rfl
    | some e => simp only [leaderRow, sgn, hS e.val e.2]
  have e : (qM (withSize M)).row (some i) t = (qM (withSize M)).row (some i) t' := by
    rw [← hc]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, key]
  simpa [qM, withSize, Matrix.row] using e

end Leader

end Intensity

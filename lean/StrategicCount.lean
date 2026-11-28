/-
  The frame of *Strategic Information* (`notes/strategic-information/README.md`,
  Section 2): the strategic count as a matrix with whole entries acting on
  histograms of types, the Proposition (counts) and the Lemma (one voter).

  Setting. Types form a finite set T. At a fixed poll each type casts one
  ballot, and the count of a profile is the sum of the counts of its ballots,
  so the strategic count of a histogram h : T → ℕ of types is M h for a matrix
  M with whole entries, one column per type (`cnt`; `ofBallots` builds M from
  the ballots and their counts). The size of the electorate, if wanted, is a
  row of M.

  * `FunctionOf MA MB`: on every profile the count of A is a function of the
    count of B, that is, histograms with the same count under B have the same
    count under A (deterministic experiments).
  * `functionOf_iff_ker`: this holds exactly when the kernel of M_B over the
    rationals lies in that of M_A. The work is the note's step from vectors
    of whole numbers to rational vectors: clear the denominators
    (`clear_den`) and split a whole vector into two histograms.
  * `functionOf_iff_rows` (the Proposition): exactly when every row of M_A is
    a rational combination of the rows of M_B, M_A = K M_B.
  * `one_voter`, `one_voter_conv` (the Lemma): if a single ballot's count
    under A tells the ballot (`Function.Injective cA`), then a function between
    the counts gives a function between the ballots, voter by voter; and if
    the count of B is the histogram of its ballots, a function between the
    ballots gives one between the counts.
-/

module

public import Mathlib

@[expose] public section

open Finset Matrix

namespace StrategicCount

variable {T ι κ : Type*} [Fintype T]

/-- The strategic count of a histogram of types. -/
def cnt (M : Matrix ι T ℤ) (h : T → ℕ) : ι → ℤ := M *ᵥ fun t => (h t : ℤ)

/-- On every profile the count of A is a function of the count of B. -/
def FunctionOf (MA : Matrix ι T ℤ) (MB : Matrix κ T ℤ) : Prop :=
  ∀ h h' : T → ℕ, cnt MB h = cnt MB h' → cnt MA h = cnt MA h'

/-- The matrix over the rationals. -/
def qM (M : Matrix ι T ℤ) : Matrix ι T ℚ := M.map (Int.cast)

lemma cast_mulVec (M : Matrix ι T ℤ) (x : T → ℤ) (i : ι) :
    (((M *ᵥ x) i : ℤ) : ℚ) = (qM M *ᵥ fun t => (x t : ℚ)) i := by
  simp [qM, Matrix.mulVec, dotProduct]

/-- Clearing denominators: a multiple of a rational vector by a positive whole
    number has whole entries. -/
lemma clear_den (v : T → ℚ) : ∃ d : ℕ, 0 < d ∧ ∃ w : T → ℤ, ∀ t, (d : ℚ) * v t = w t := by
  classical
  refine ⟨∏ t, (v t).den, Finset.prod_pos fun t _ => (v t).den_pos,
    fun t => (∏ s ∈ univ.erase t, (v s).den : ℕ) * (v t).num, fun t => ?_⟩
  rw [← Finset.mul_prod_erase univ (fun s => (v s).den) (mem_univ t)]
  have key : v t * (v t).den = (v t).num := Rat.mul_den_eq_num (v t)
  push_cast
  linear_combination (∏ s ∈ univ.erase t, ((v s).den : ℚ)) * key

/-- **Kernels.** The count of A is a function of the count of B exactly when the
    rational kernel of M_B lies in that of M_A. -/
theorem functionOf_iff_ker (MA : Matrix ι T ℤ) (MB : Matrix κ T ℤ) :
    FunctionOf MA MB ↔ ∀ v : T → ℚ, qM MB *ᵥ v = 0 → qM MA *ᵥ v = 0 := by
  constructor
  · intro hF v hv
    obtain ⟨d, hd, w, hw⟩ := clear_den v
    have e1 : (fun t => (w t : ℚ)) = (d : ℚ) • v := funext fun t => by
      rw [Pi.smul_apply, smul_eq_mul, hw t]
    -- the whole vector w lies in the kernel of M_B
    have hBq : qM MB *ᵥ (fun t => (w t : ℚ)) = 0 := by
      rw [e1, Matrix.mulVec_smul, hv, smul_zero]
    have hBw : MB *ᵥ w = 0 := by
      funext i
      have h := congr_fun hBq i
      rw [← cast_mulVec, Pi.zero_apply] at h
      rw [Pi.zero_apply]
      exact_mod_cast h
    -- w is the difference of two histograms
    let hp : T → ℕ := fun t => (w t).toNat
    let hn : T → ℕ := fun t => (-w t).toNat
    have hw' : w = (fun t => (hp t : ℤ)) - fun t => (hn t : ℤ) := by
      funext t
      simp only [Pi.sub_apply, hp, hn]
      exact (Int.toNat_sub_toNat_neg (w t)).symm
    have hB : cnt MB hp = cnt MB hn := by
      unfold cnt
      rw [← sub_eq_zero, ← Matrix.mulVec_sub, ← hw', hBw]
    have hA : MA *ᵥ w = 0 := by
      rw [hw', Matrix.mulVec_sub, sub_eq_zero]
      exact hF hp hn hB
    have hAq : (d : ℚ) • (qM MA *ᵥ v) = 0 := by
      rw [← Matrix.mulVec_smul, ← e1]
      funext i
      rw [← cast_mulVec, hA]
      simp
    rcases smul_eq_zero.mp hAq with h | h
    · exact absurd h (by exact_mod_cast hd.ne')
    · exact h
  · intro hK h h' hh
    have hv : qM MB *ᵥ ((fun t => ((h t : ℤ) : ℚ)) - fun t => ((h' t : ℤ) : ℚ)) = 0 := by
      rw [Matrix.mulVec_sub, sub_eq_zero]
      funext i
      rw [← cast_mulVec, ← cast_mulVec]
      exact congrArg (fun x : κ → ℤ => ((x i : ℤ) : ℚ)) hh
    have hA := hK _ hv
    rw [Matrix.mulVec_sub, sub_eq_zero] at hA
    funext i
    show (MA *ᵥ fun t => ((h t : ℕ) : ℤ)) i = (MA *ᵥ fun t => ((h' t : ℕ) : ℤ)) i
    have := congr_fun hA i
    rw [← cast_mulVec, ← cast_mulVec] at this
    exact_mod_cast this

/-- A linear map whose kernel contains that of another factors through it. -/
lemma factor {V W U : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    [AddCommGroup U] [Module ℚ U] (f : V →ₗ[ℚ] W) (g : V →ₗ[ℚ] U)
    (h : LinearMap.ker f ≤ LinearMap.ker g) : ∃ k : W →ₗ[ℚ] U, ∀ x, g x = k (f x) := by
  obtain ⟨k, hk⟩ := LinearMap.exists_extend
    ((LinearMap.ker f).liftQ g h ∘ₗ f.quotKerEquivRange.symm.toLinearMap)
  refine ⟨k, fun x => ?_⟩
  have e := LinearMap.congr_fun hk ⟨f x, LinearMap.mem_range_self f x⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe] at e
  rw [e]
  have hq : f.quotKerEquivRange.symm ⟨f x, LinearMap.mem_range_self f x⟩ =
      Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext (LinearMap.quotKerEquivRange_apply_mk f x).symm
  rw [hq, Submodule.liftQ_apply]

/-- **The Proposition (counts).** The count of A is a function of the count of
    B on every profile exactly when every row of M_A is a combination of rows
    of M_B. -/
theorem functionOf_iff_rows [Fintype κ] [DecidableEq κ] [DecidableEq T]
    (MA : Matrix ι T ℤ) (MB : Matrix κ T ℤ) :
    FunctionOf MA MB ↔ ∃ K : Matrix ι κ ℚ, qM MA = K * qM MB := by
  rw [functionOf_iff_ker]
  constructor
  · intro hK
    obtain ⟨k, hk⟩ := factor (qM MB).mulVecLin (qM MA).mulVecLin (fun v hv => by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
      exact hK v hv)
    refine ⟨LinearMap.toMatrix' k, ?_⟩
    have hv : ∀ v, qM MA *ᵥ v = (LinearMap.toMatrix' k * qM MB) *ᵥ v := fun v => by
      rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
      exact hk v
    ext i t
    have := congr_fun (hv (Pi.single t 1)) i
    simpa [Matrix.mulVec_single] using this
  · rintro ⟨K, hK⟩ v hv
    rw [hK, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

/-! ### The Lemma (one voter) -/

/-- The matrix of a method at a poll: type t casts ballot β t, whose count is
    c (β t). -/
def ofBallots {Bal : Type*} (c : Bal → ι → ℤ) (β : T → Bal) : Matrix ι T ℤ :=
  fun i t => c (β t) i

/-- **The Lemma (one voter).** If a single ballot's count under A tells the
    ballot, and the count of A is a function of the count of B, then the
    strategic ballot of A is a function of that of B, voter by voter. -/
theorem one_voter [DecidableEq T] {BA BB : Type*} (cA : BA → ι → ℤ) (cB : BB → κ → ℤ)
    (βA : T → BA) (βB : T → BB) (hinj : Function.Injective cA)
    (hF : FunctionOf (ofBallots cA βA) (ofBallots cB βB)) :
    ∀ t t', βB t = βB t' → βA t = βA t' := by
  intro t t' h
  have key := hF (Pi.single t 1) (Pi.single t' 1) (by
    funext i
    simp [cnt, ofBallots, Matrix.mulVec, dotProduct, Pi.single_apply, h])
  apply hinj
  funext i
  have := congr_fun key i
  simpa [cnt, ofBallots, Matrix.mulVec, dotProduct, Pi.single_apply] using this

/-- **The converse.** If the count of B is the histogram of its ballots, a
    function between the ballots gives one between the counts. -/
theorem one_voter_conv {BA BB : Type*} [Fintype BB] [DecidableEq BB] (cA : BA → ι → ℤ)
    (φ : BB → BA) (βB : T → BB) :
    FunctionOf (ofBallots cA (φ ∘ βB)) (ofBallots (fun b b' => if b' = b then (1 : ℤ) else 0) βB) := by
  have key : ∀ h : T → ℕ, cnt (ofBallots cA (φ ∘ βB)) h = fun i =>
      ∑ b, cA (φ b) i * cnt (ofBallots (fun b b' => if b' = b then (1 : ℤ) else 0) βB) h b := by
    intro h
    funext i
    simp only [cnt, ofBallots, Matrix.mulVec, dotProduct, Function.comp_apply]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun t _ => ?_
    simp [ite_mul, mul_ite]
  intro h h' hh
  rw [key, key, hh]

end StrategicCount

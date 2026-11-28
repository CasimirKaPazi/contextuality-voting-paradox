/-
  Lemma 1 and the first parts of Propositions 2 and 7 of *Bounds from Criteria*
  (`notes/strategic-information/bounds.md`, Sections 1, 2 and 5), in the frame
  of `StrategicCount.lean`.

  Setting. Types T, a strategic count M with whole entries, and a family of
  margins μ e : T → ℤ, one for each comparison e in question: for the leader a,
  the comparisons of a with every other candidate x; for a graph G, its edges.
  The margin of a histogram is `marg`, its size `size`. A method certifies the
  comparisons (`Certifies`) if two histograms with the same strategic count and
  the same size never differ in whether a margin is positive.

  * `lemma1_abstract`: if some histogram with every type present has all
    margins zero, certification holds exactly when every rational vector in
    the kernel of M with entries adding up to zero lies in the kernel of every
    margin (`KerCond`). The proof is the note's: clear denominators, and
    compare h + w with h − w for a multiple h of the balanced histogram.
  * `kerCond_iff_rows`: the kernel condition says that every margin is a
    rational combination of the rows of M and the size of the electorate.
  * `same_column`: under certification two types with the same column of M,
    in particular with the same strategic ballot, have the same margins
    (the first part of Propositions 2 and 7).
  * Rankings. With rankings as permutations of `Fin m` (the position of each
    candidate, smaller is better) and the margin of x over y as ±1
    (`sgn`), every margin sums to zero over all rankings (`sum_sgn`), so if
    every ranking occurs among the types there is a balanced histogram
    (`balanced`), and Lemma 1 holds for every family of pairs (`lemma1`,
    `same_pref`).

  Not here: the counts 2^(m−1) and a(G) of Propositions 2 and 7, the ranks of
  Propositions 3 and 7, and Corollary 8.
-/

module

public import Mathlib
public import StrategicCount

@[expose] public section

open Finset Matrix StrategicCount

namespace Certification

variable {T ι E : Type*} [Fintype T]

/-- The size of the electorate. -/
def size (h : T → ℕ) : ℕ := ∑ t, h t

/-- The margin of a histogram. -/
def marg (μ : T → ℤ) (h : T → ℕ) : ℤ := ∑ t, μ t * h t

/-- The strategic count, with the size, determines whether each margin is
    positive. -/
def Certifies (M : Matrix ι T ℤ) (μ : E → T → ℤ) : Prop :=
  ∀ h h' : T → ℕ, cnt M h = cnt M h' → size h = size h' → ∀ e,
    0 < marg (μ e) h → 0 < marg (μ e) h'

/-- Every rational vector in the kernel of M, with entries adding up to zero,
    lies in the kernel of every margin. -/
def KerCond (M : Matrix ι T ℤ) (μ : E → T → ℤ) : Prop :=
  ∀ v : T → ℚ, qM M *ᵥ v = 0 → ∑ t, v t = 0 → ∀ e, ∑ t, (μ e t : ℚ) * v t = 0

lemma cnt_eq_of {M : Matrix ι T ℤ} {h h' : T → ℕ}
    (hv : qM M *ᵥ ((fun t => ((h t : ℤ) : ℚ)) - fun t => ((h' t : ℤ) : ℚ)) = 0) :
    cnt M h = cnt M h' := by
  rw [Matrix.mulVec_sub, sub_eq_zero] at hv
  funext i
  show (M *ᵥ fun t => ((h t : ℕ) : ℤ)) i = (M *ᵥ fun t => ((h' t : ℕ) : ℤ)) i
  have := congr_fun hv i
  rw [← cast_mulVec, ← cast_mulVec] at this
  exact_mod_cast this

/-- **Lemma 1, abstract form.** -/
theorem lemma1_abstract (M : Matrix ι T ℤ) (μ : E → T → ℤ) (h0 : T → ℕ) (hpos : ∀ t, 0 < h0 t)
    (hz : ∀ e, marg (μ e) h0 = 0) : Certifies M μ ↔ KerCond M μ := by
  constructor
  · intro hC v hv hs e
    by_contra hne
    obtain ⟨d, hd, w, hw⟩ := clear_den v
    have e1 : (fun t => (w t : ℚ)) = (d : ℚ) • v := funext fun t => by
      rw [Pi.smul_apply, smul_eq_mul, hw t]
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    -- w is in the kernel of M, sums to zero, and has a margin of either sign
    have hMw : M *ᵥ w = 0 := by
      funext i
      have h := congr_fun (show qM M *ᵥ (fun t => (w t : ℚ)) = 0 by
        rw [e1, Matrix.mulVec_smul, hv, smul_zero]) i
      rw [← cast_mulVec, Pi.zero_apply] at h
      rw [Pi.zero_apply]
      exact_mod_cast h
    have hsw : ∑ t, w t = 0 := by
      have : ∑ t, (w t : ℚ) = (d : ℚ) * ∑ t, v t := by
        rw [Finset.mul_sum]
        exact sum_congr rfl fun t _ => (hw t).symm
      rw [hs, mul_zero] at this
      exact_mod_cast this
    have hmw : ∑ t, μ e t * w t ≠ 0 := by
      intro h0'
      apply hne
      have : ((∑ t, μ e t * w t : ℤ) : ℚ) = (d : ℚ) * ∑ t, (μ e t : ℚ) * v t := by
        push_cast
        rw [Finset.mul_sum]
        exact sum_congr rfl fun t _ => by rw [← hw t]; ring
      rw [h0', Int.cast_zero] at this
      rcases mul_eq_zero.mp this.symm with h | h
      · exact absurd h hdq
      · exact h
    -- the two histograms N h0 + w and N h0 − w
    let N : ℕ := ∑ t, (w t).natAbs
    have hN : ∀ t, ((w t).natAbs : ℤ) ≤ N := fun t => by
      exact_mod_cast single_le_sum (f := fun t => (w t).natAbs) (fun _ _ => Nat.zero_le _)
        (mem_univ t)
    have hle : ∀ t, |w t| ≤ (N : ℤ) * h0 t := fun t => by
      have h1 : (1 : ℤ) ≤ h0 t := by exact_mod_cast hpos t
      have h2 := hN t
      have h3 : (0 : ℤ) ≤ N := by positivity
      rw [Int.abs_eq_natAbs]
      nlinarith [mul_nonneg h3 (sub_nonneg.mpr h1)]
    let hp : T → ℕ := fun t => ((N : ℤ) * h0 t + w t).toNat
    let hn : T → ℕ := fun t => ((N : ℤ) * h0 t - w t).toNat
    have ep : ∀ t, ((hp t : ℕ) : ℤ) = N * h0 t + w t := fun t =>
      Int.toNat_of_nonneg (by have := neg_abs_le (w t); linarith [hle t])
    have en : ∀ t, ((hn t : ℕ) : ℤ) = N * h0 t - w t := fun t =>
      Int.toNat_of_nonneg (by have := le_abs_self (w t); linarith [hle t])
    have hcnt : cnt M hp = cnt M hn := by
      unfold cnt
      have : (fun t => ((hp t : ℕ) : ℤ)) = (fun t => ((hn t : ℕ) : ℤ)) + 2 • w := by
        funext t
        simp only [Pi.add_apply, Pi.smul_apply, ep, en]
        ring
      rw [this, Matrix.mulVec_add, Matrix.mulVec_smul, hMw, smul_zero, add_zero]
    have hsize : size hp = size hn := by
      have : ((size hp : ℕ) : ℤ) = (size hn : ℤ) := by
        unfold size
        push_cast
        simp only [ep, en, sum_add_distrib, sum_sub_distrib, hsw, add_zero, sub_zero]
      exact_mod_cast this
    have mz : ∑ t, μ e t * ((N : ℤ) * h0 t) = 0 := by
      have := hz e
      unfold marg at this
      rw [show ∑ t, μ e t * ((N : ℤ) * h0 t) = N * ∑ t, μ e t * h0 t by
        rw [Finset.mul_sum]; exact sum_congr rfl fun t _ => by ring, this, mul_zero]
    have mp : marg (μ e) hp = ∑ t, μ e t * w t := by
      unfold marg
      simp only [ep, mul_add]
      rw [sum_add_distrib, mz, zero_add]
    have mn : marg (μ e) hn = -∑ t, μ e t * w t := by
      unfold marg
      simp only [en, mul_sub]
      rw [sum_sub_distrib, mz, zero_sub]
    rcases lt_or_gt_of_ne hmw with hl | hl
    · have := hC hn hp hcnt.symm hsize.symm e (by rw [mn]; linarith)
      rw [mp] at this
      linarith
    · have := hC hp hn hcnt hsize e (by rw [mp]; linarith)
      rw [mn] at this
      linarith
  · intro hK h h' hc hs e hp
    have hv : qM M *ᵥ ((fun t => ((h t : ℤ) : ℚ)) - fun t => ((h' t : ℤ) : ℚ)) = 0 := by
      rw [Matrix.mulVec_sub, sub_eq_zero]
      funext i
      rw [← cast_mulVec, ← cast_mulVec]
      exact congrArg (fun x : ι → ℤ => ((x i : ℤ) : ℚ)) hc
    have hsum : ∑ t, ((fun t => ((h t : ℤ) : ℚ)) - fun t => ((h' t : ℤ) : ℚ)) t = 0 := by
      simp only [Pi.sub_apply, sum_sub_distrib]
      have : ((size h : ℕ) : ℚ) = (size h' : ℚ) := by rw [hs]
      unfold size at this
      push_cast at this ⊢
      rw [this, sub_self]
    have hm := hK _ hv hsum e
    simp only [Pi.sub_apply, mul_sub, sum_sub_distrib, sub_eq_zero] at hm
    have : ((marg (μ e) h : ℤ) : ℚ) = (marg (μ e) h' : ℚ) := by
      unfold marg
      push_cast at hm ⊢
      exact hm
    have h2 : marg (μ e) h = marg (μ e) h' := by exact_mod_cast this
    rwa [← h2]

/-- The strategic count with the size of the electorate as an extra row. -/
def withSize (M : Matrix ι T ℤ) : Matrix (Option ι) T ℤ := fun i t =>
  match i with
  | none => 1
  | some i => M i t

/-- The margins as a matrix, one row per comparison. -/
def margM (μ : E → T → ℤ) : Matrix E T ℤ := μ

omit [Fintype T] in
lemma qM_margM (μ : E → T → ℤ) (e : E) (t : T) : qM (margM μ) e t = (μ e t : ℚ) := rfl

/-- **Lemma 1, rows.** The kernel condition says that every margin is a rational
    combination of the rows of M and the size of the electorate. -/
theorem kerCond_iff_rows [Fintype ι] [DecidableEq ι] [DecidableEq T] (M : Matrix ι T ℤ)
    (μ : E → T → ℤ) :
    KerCond M μ ↔ ∃ K : Matrix E (Option ι) ℚ, qM (margM μ) = K * qM (withSize M) := by
  rw [← functionOf_iff_rows (margM μ) (withSize M), functionOf_iff_ker]
  have key : ∀ v : T → ℚ, qM (withSize M) *ᵥ v = 0 ↔ qM M *ᵥ v = 0 ∧ ∑ t, v t = 0 := by
    intro v
    constructor
    · intro h
      refine ⟨funext fun i => ?_, ?_⟩
      · have := congr_fun h (some i)
        simpa [qM, withSize, Matrix.mulVec, dotProduct] using this
      · have := congr_fun h none
        simpa [qM, withSize, Matrix.mulVec, dotProduct] using this
    · rintro ⟨h1, h2⟩
      funext i
      cases i with
      | none => simpa [qM, withSize, Matrix.mulVec, dotProduct] using h2
      | some i =>
        have := congr_fun h1 i
        simpa [qM, withSize, Matrix.mulVec, dotProduct] using this
  constructor
  · intro hK v hv
    obtain ⟨h1, h2⟩ := (key v).mp hv
    funext e
    have := hK v h1 h2 e
    simpa [qM_margM, Matrix.mulVec, dotProduct] using this
  · intro hK v h1 h2 e
    have := congr_fun (hK v ((key v).mpr ⟨h1, h2⟩)) e
    simpa [qM_margM, Matrix.mulVec, dotProduct] using this

/-- **Same column, same margins** (the first part of Propositions 2 and 7). -/
theorem same_column [DecidableEq T] {M : Matrix ι T ℤ} {μ : E → T → ℤ} (hK : KerCond M μ)
    {t t' : T} (hcol : ∀ i, M i t = M i t') (e : E) : μ e t = μ e t' := by
  have h := hK (Pi.single t 1 - Pi.single t' 1) (by
      funext i
      simp [qM, Matrix.mulVec, dotProduct, Pi.single_apply, mul_sub, sum_sub_distrib, hcol i])
    (by simp [sum_sub_distrib]) e
  simp [mul_sub, sum_sub_distrib, Pi.single_apply, sub_eq_zero] at h
  exact_mod_cast h

/-! ### Rankings -/

variable {m : ℕ}

/-- The margin of x over y for a voter with ranking σ (σ gives each candidate
    its position, smaller is better): +1 if the voter prefers x, −1 otherwise. -/
def sgn (σ : Equiv.Perm (Fin m)) (x y : Fin m) : ℤ := if σ x < σ y then 1 else -1

/-- Every margin sums to zero over all rankings: exchanging x and y is a
    bijection that reverses it. -/
lemma sum_sgn {x y : Fin m} (hxy : x ≠ y) : ∑ σ : Equiv.Perm (Fin m), sgn σ x y = 0 := by
  have hS : ∑ σ : Equiv.Perm (Fin m), sgn σ x y = ∑ σ : Equiv.Perm (Fin m), -sgn σ x y := by
    rw [← Equiv.sum_comp (Equiv.mulRight (Equiv.swap x y))]
    refine sum_congr rfl fun σ _ => ?_
    simp only [Equiv.coe_mulRight, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, sgn]
    have hne : σ y ≠ σ x := fun h => hxy (σ.injective h).symm
    rcases lt_trichotomy (σ x) (σ y) with h | h | h
    · simp [h, not_lt.mpr h.le]
    · exact absurd h.symm hne
    · simp [h, not_lt.mpr h.le]
  rw [sum_neg_distrib] at hS
  linarith

variable (ρ : T → Equiv.Perm (Fin m))

/-- The balanced histogram: every ranking gets the same total K, divided
    equally among its types. -/
noncomputable def balanced : T → ℕ := by
  classical
  exact fun t => (∏ r : Equiv.Perm (Fin m), (univ.filter fun s => ρ s = r).card) /
    (univ.filter fun s => ρ s = ρ t).card

lemma balanced_spec (hρ : Function.Surjective ρ) :
    (∀ t, 0 < balanced ρ t) ∧ ∀ x y : Fin m, x ≠ y →
      marg (fun t => sgn (ρ t) x y) (balanced ρ) = 0 := by
  classical
  set c : Equiv.Perm (Fin m) → ℕ := fun r => (univ.filter fun s => ρ s = r).card with hc
  have cpos : ∀ r, 0 < c r := fun r => by
    obtain ⟨t, ht⟩ := hρ r
    exact card_pos.mpr ⟨t, by simp [ht]⟩
  set K : ℕ := ∏ r, c r with hK
  have cdvd : ∀ r, c r ∣ K := fun r => dvd_prod_of_mem c (mem_univ r)
  have hb : ∀ t, balanced ρ t = K / c (ρ t) := fun t => rfl
  refine ⟨fun t => ?_, fun x y hxy => ?_⟩
  · rw [hb]
    exact Nat.div_pos (Nat.le_of_dvd (prod_pos fun r _ => cpos r) (cdvd _)) (cpos _)
  · simp only [marg]
    rw [← Finset.sum_fiberwise univ ρ (fun t => sgn (ρ t) x y * (balanced ρ t : ℤ))]
    have inner : ∀ r, ∑ t ∈ univ.filter (fun t => ρ t = r), sgn (ρ t) x y * (balanced ρ t : ℤ) =
        sgn r x y * K := fun r => by
      have e : ∀ t ∈ univ.filter (fun t => ρ t = r),
          sgn (ρ t) x y * (balanced ρ t : ℤ) = sgn r x y * ((K / c r : ℕ) : ℤ) := fun t ht => by
        have hr := (mem_filter.mp ht).2
        rw [hb, hr]
      rw [sum_congr rfl e, sum_const, nsmul_eq_mul]
      have : ((c r : ℕ) : ℤ) * ((K / c r : ℕ) : ℤ) = K := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' (cdvd r)]
      change ((c r : ℕ) : ℤ) * (sgn r x y * ((K / c r : ℕ) : ℤ)) = sgn r x y * K
      linear_combination (sgn r x y) * this
    rw [sum_congr rfl fun r _ => inner r, ← sum_mul, sum_sgn hxy, zero_mul]

/-- **Lemma 1.** If every ranking occurs among the types, certifying a family
    of comparisons (x e, y e) is the kernel condition. -/
theorem lemma1 (hρ : Function.Surjective ρ) (M : Matrix ι T ℤ) (x y : E → Fin m)
    (hxy : ∀ e, x e ≠ y e) :
    Certifies M (fun e t => sgn (ρ t) (x e) (y e)) ↔
      KerCond M (fun e t => sgn (ρ t) (x e) (y e)) :=
  lemma1_abstract M _ (balanced ρ) (balanced_spec ρ hρ).1
    fun e => (balanced_spec ρ hρ).2 _ _ (hxy e)

/-- **The ballot tells the comparisons** (Propositions 2 and 7, first part): if
    the comparisons are certified, two types with the same column of M agree
    on every compared pair. -/
theorem same_pref [DecidableEq T] (hρ : Function.Surjective ρ) {M : Matrix ι T ℤ}
    {x y : E → Fin m} (hxy : ∀ e, x e ≠ y e)
    (hC : Certifies M (fun e t => sgn (ρ t) (x e) (y e))) {t t' : T}
    (hcol : ∀ i, M i t = M i t') (e : E) : (ρ t (x e) < ρ t (y e) ↔ ρ t' (x e) < ρ t' (y e)) := by
  have h := same_column ((lemma1 ρ hρ M x y hxy).mp hC) hcol e
  simp only [sgn] at h
  by_cases h1 : ρ t (x e) < ρ t (y e) <;> by_cases h2 : ρ t' (x e) < ρ t' (y e) <;>
    simp [h1, h2] at h ⊢

end Certification

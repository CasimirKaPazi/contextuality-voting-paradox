module

public import Mathlib

@[expose] public section

/-!
# Probabilistic Arrow for three alternatives

Theorem 5 of *Four Levels of Obstruction in Social Choice*: every empirical model on Arrow's
scenario with three alternatives is a mixture of dictatorships, for any finite set of voters.

Encoding. The pairs ab, bc, ca are issues 1, 2, 3. A profile is given by its three columns
`A B C : Finset I` (the voters with bit 1 on each issue); it is admissible when no voter has all
three bits equal. At an admissible profile the model is a lottery `e A B C x y z` over social
triples `(x, y, z)`; it gives probability zero to `000` and `111`.

Full compatibility is encoded by the types of the marginals: the probability `p1 A` of social bit
1 on issue 1 depends only on column `A`, and the joint probability `q12 A B` of social bit 1 on
issues 1 and 2 depends only on columns `A` and `B` (likewise for the other issues and pairs).
Unanimity: `p_j univ = 1` and `p_j ∅ = 0`.
-/

open Finset

namespace ArrowProb

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- No voter has all three bits equal. -/
def Adm (A B C : Finset I) : Prop :=
  ∀ k, ¬ (k ∈ A ∧ k ∈ B ∧ k ∈ C) ∧ ¬ (k ∉ A ∧ k ∉ B ∧ k ∉ C)

omit [Fintype I] [DecidableEq I] in
lemma Adm.rot {A B C : Finset I} (h : Adm A B C) : Adm B C A := by
  intro k
  obtain ⟨h1, h2⟩ := h k
  exact ⟨fun ⟨hb, hc, ha⟩ => h1 ⟨ha, hb, hc⟩, fun ⟨hb, hc, ha⟩ => h2 ⟨ha, hb, hc⟩⟩

lemma adm_W0 (A B : Finset I) : Adm A B (A ∪ B)ᶜ := by
  intro k; refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp at h <;> tauto

lemma adm_Wstar (A B : Finset I) : Adm A B (A ∩ B)ᶜ := by
  intro k; refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp at h <;> tauto

lemma adm_univ_left (A B : Finset I) : Adm univ B (A ∪ B)ᶜ := by
  intro k; refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp at h; tauto

lemma adm_univ_mid (A B : Finset I) : Adm A univ (A ∪ B)ᶜ := by
  intro k; refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp at h; tauto

omit [DecidableEq I] in
lemma adm_empty_mid (A : Finset I) : Adm A ∅ univ := by
  intro k; refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp at h

omit [DecidableEq I] in
lemma adm_empty_left (B : Finset I) : Adm ∅ B univ := by
  intro k; refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp at h

/-- The empirical model and its marginals, at every admissible profile. -/
def Model (e : Finset I → Finset I → Finset I → Bool → Bool → Bool → ℝ)
    (p1 p2 p3 : Finset I → ℝ) (q12 q23 q31 : Finset I → Finset I → ℝ) : Prop :=
  ∀ A B C, Adm A B C →
    (∀ x y z, 0 ≤ e A B C x y z) ∧ e A B C false false false = 0 ∧ e A B C true true true = 0 ∧
    (∑ x, ∑ y, ∑ z, e A B C x y z) = 1 ∧
    p1 A = ∑ y, ∑ z, e A B C true y z ∧ p2 B = ∑ x, ∑ z, e A B C x true z ∧
    p3 C = ∑ x, ∑ y, e A B C x y true ∧
    q12 A B = ∑ z, e A B C true true z ∧ q23 B C = ∑ x, e A B C x true true ∧
    q31 C A = ∑ y, e A B C true y true

/-- The linear facts used in the proof, for one cyclic orientation of the issues. -/
structure Facts (P1 P2 P3 : Finset I → ℝ) (Q12 Q23 Q31 : Finset I → Finset I → ℝ) : Prop where
  star : ∀ A B C, Adm A B C → Q12 A B + Q23 B C + Q31 C A = P1 A + P2 B + P3 C - 1
  b3 : ∀ A B C, Adm A B C → Q12 A B ≤ 1 - P3 C
  b1 : ∀ A B C, Adm A B C → Q23 B C ≤ 1 - P1 A
  b2 : ∀ A B C, Adm A B C → Q31 C A ≤ 1 - P2 B
  n12 : ∀ A B C, Adm A B C → 0 ≤ Q12 A B
  n23 : ∀ A B C, Adm A B C → 0 ≤ Q23 B C
  n31 : ∀ A B C, Adm A B C → 0 ≤ Q31 C A
  l12 : ∀ A B C, Adm A B C → Q12 A B ≤ P1 A
  r12 : ∀ A B C, Adm A B C → Q12 A B ≤ P2 B
  l23 : ∀ A B C, Adm A B C → Q23 B C ≤ P2 B
  r23 : ∀ A B C, Adm A B C → Q23 B C ≤ P3 C
  l31 : ∀ A B C, Adm A B C → Q31 C A ≤ P3 C
  r31 : ∀ A B C, Adm A B C → Q31 C A ≤ P1 A

section
variable {e : Finset I → Finset I → Finset I → Bool → Bool → Bool → ℝ}
  {p1 p2 p3 : Finset I → ℝ} {q12 q23 q31 : Finset I → Finset I → ℝ}

omit [Fintype I] [DecidableEq I] in
theorem facts_of_model (hM : Model e p1 p2 p3 q12 q23 q31) : Facts p1 p2 p3 q12 q23 q31 := by
  have key : ∀ A B C, Adm A B C →
      (q12 A B + q23 B C + q31 C A = p1 A + p2 B + p3 C - 1) ∧
      q12 A B ≤ 1 - p3 C ∧ q23 B C ≤ 1 - p1 A ∧ q31 C A ≤ 1 - p2 B ∧
      0 ≤ q12 A B ∧ 0 ≤ q23 B C ∧ 0 ≤ q31 C A ∧
      q12 A B ≤ p1 A ∧ q12 A B ≤ p2 B ∧ q23 B C ≤ p2 B ∧ q23 B C ≤ p3 C ∧
      q31 C A ≤ p3 C ∧ q31 C A ≤ p1 A := by
    intro A B C h
    obtain ⟨hn, h0, h1, hs, e1, e2, e3, f1, f2, f3⟩ := hM A B C h
    simp only [Fintype.sum_bool] at hs e1 e2 e3 f1 f2 f3
    have := hn true true true; have := hn true true false; have := hn true false true
    have := hn true false false; have := hn false true true; have := hn false true false
    have := hn false false true; have := hn false false false
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  exact
    { star := fun A B C h => (key A B C h).1
      b3 := fun A B C h => (key A B C h).2.1
      b1 := fun A B C h => (key A B C h).2.2.1
      b2 := fun A B C h => (key A B C h).2.2.2.1
      n12 := fun A B C h => (key A B C h).2.2.2.2.1
      n23 := fun A B C h => (key A B C h).2.2.2.2.2.1
      n31 := fun A B C h => (key A B C h).2.2.2.2.2.2.1
      l12 := fun A B C h => (key A B C h).2.2.2.2.2.2.2.1
      r12 := fun A B C h => (key A B C h).2.2.2.2.2.2.2.2.1
      l23 := fun A B C h => (key A B C h).2.2.2.2.2.2.2.2.2.1
      r23 := fun A B C h => (key A B C h).2.2.2.2.2.2.2.2.2.2.1
      l31 := fun A B C h => (key A B C h).2.2.2.2.2.2.2.2.2.2.2.1
      r31 := fun A B C h => (key A B C h).2.2.2.2.2.2.2.2.2.2.2.2 }

end

section
variable {P1 P2 P3 : Finset I → ℝ} {Q12 Q23 Q31 : Finset I → Finset I → ℝ}

omit [Fintype I] [DecidableEq I] in
/-- Rotating the issues 1 → 2 → 3 → 1. -/
theorem Facts.rot (F : Facts P1 P2 P3 Q12 Q23 Q31) : Facts P2 P3 P1 Q23 Q31 Q12 where
  star A B C h := by have := F.star C A B h.rot.rot; linarith
  b3 A B C h := F.b1 C A B h.rot.rot
  b1 A B C h := F.b2 C A B h.rot.rot
  b2 A B C h := F.b3 C A B h.rot.rot
  n12 A B C h := F.n23 C A B h.rot.rot
  n23 A B C h := F.n31 C A B h.rot.rot
  n31 A B C h := F.n12 C A B h.rot.rot
  l12 A B C h := F.l23 C A B h.rot.rot
  r12 A B C h := F.r23 C A B h.rot.rot
  l23 A B C h := F.l31 C A B h.rot.rot
  r23 A B C h := F.r31 C A B h.rot.rot
  l31 A B C h := F.l12 C A B h.rot.rot
  r31 A B C h := F.r12 C A B h.rot.rot

/-- The joint probability is computed at the smallest admissible third column `(A ∪ B)ᶜ`. -/
theorem Facts.K (F : Facts P1 P2 P3 Q12 Q23 Q31) (h1 : P1 univ = 1) (h2 : P2 univ = 1)
    (A B : Finset I) : Q12 A B = P1 A + P2 B + P3 (A ∪ B)ᶜ - 1 := by
  have hs := F.star A B _ (adm_W0 A B)
  have u23 := F.b1 univ B _ (adm_univ_left A B)
  have u31 := F.b2 A univ _ (adm_univ_mid A B)
  have z23 := F.n23 A B _ (adm_W0 A B)
  have z31 := F.n31 A B _ (adm_W0 A B)
  rw [h1] at u23; rw [h2] at u31
  linarith

/-- Unanimity on one issue ties the functions of two issues. -/
theorem Facts.E (F : Facts P1 P2 P3 Q12 Q23 Q31) (h1 : P1 univ = 1) (h2 : P2 univ = 1)
    (e1 : P1 ∅ = 0) (e2 : P2 ∅ = 0) :
    (∀ A, P1 A = 1 - P3 Aᶜ) ∧ (∀ B, P2 B = 1 - P3 Bᶜ) := by
  constructor
  · intro A
    have hk := F.K h1 h2 A ∅
    have hr := F.r12 A ∅ univ (adm_empty_mid A)
    have hn := F.n12 A ∅ univ (adm_empty_mid A)
    rw [Finset.union_empty] at hk
    linarith
  · intro B
    have hk := F.K h1 h2 ∅ B
    have hl := F.l12 ∅ B univ (adm_empty_left B)
    have hn := F.n12 ∅ B univ (adm_empty_left B)
    rw [Finset.empty_union] at hk
    linarith

end

/-- **Theorem 5.** Every empirical model on Arrow's scenario with three alternatives is a mixture
of dictatorships: there are weights `w k ≥ 0` summing to 1 such that at every admissible profile
the probability of each social triple is the total weight of the voters with that ranking. -/
theorem mixture_of_dictatorships
    (e : Finset I → Finset I → Finset I → Bool → Bool → Bool → ℝ)
    (p1 p2 p3 : Finset I → ℝ) (q12 q23 q31 : Finset I → Finset I → ℝ)
    (hM : Model e p1 p2 p3 q12 q23 q31)
    (u1 : p1 univ = 1) (u2 : p2 univ = 1) (u3 : p3 univ = 1)
    (z1 : p1 ∅ = 0) (z2 : p2 ∅ = 0) (z3 : p3 ∅ = 0) :
    ∃ w : I → ℝ, (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧
      ∀ A B C, Adm A B C → ∀ x y z, e A B C x y z =
        ∑ k, if (decide (k ∈ A) = x ∧ decide (k ∈ B) = y ∧ decide (k ∈ C) = z) then w k else 0 := by
  have F := facts_of_model hM
  have F2 := F.rot
  have F3 := F2.rot
  obtain ⟨E1a, E1b⟩ := F.E u1 u2 z1 z2
  obtain ⟨E2a, E2b⟩ := F2.E u2 u3 z2 z3
  -- all three issues carry the same function β = p1
  have h12 : ∀ A, p2 A = p1 A := fun A => by rw [E1a A, E1b A]
  have h32 : ∀ A, p3 A = p2 A := fun A => by rw [E2a A, E2b A]
  have hc : ∀ A, p1 A = 1 - p1 Aᶜ := fun A => by rw [← h12 A, E2a A]
  have hcc : ∀ A, p1 Aᶜ = 1 - p1 A := fun A => by have := hc Aᶜ; rw [compl_compl] at this; exact this
  -- every joint probability is β A + β B - β (A ∪ B)
  have hq12 : ∀ A B, q12 A B = p1 A + p1 B - p1 (A ∪ B) := fun A B => by
    have := F.K u1 u2 A B; rw [h12, h32, h12, hcc] at this; linarith
  have hq23 : ∀ A B, q23 A B = p1 A + p1 B - p1 (A ∪ B) := fun A B => by
    have := F2.K u2 u3 A B; rw [h12, h32, h12] at this; rw [hcc] at this; linarith
  have hq31 : ∀ A B, q31 A B = p1 A + p1 B - p1 (A ∪ B) := fun A B => by
    have := F3.K u3 u1 A B; rw [h32, h12, h12, hcc] at this; linarith
  -- additivity on disjoint sets
  have hadd : ∀ A B : Finset I, Disjoint A B → p1 (A ∪ B) = p1 A + p1 B := by
    intro A B hd
    have hub := F.b3 A B _ (adm_Wstar A B)
    have hn := F.n12 A B _ (adm_Wstar A B)
    rw [h32, h12, hcc, Finset.disjoint_iff_inter_eq_empty.mp hd, z1] at hub
    rw [hq12] at hub hn
    linarith
  obtain ⟨w, hw⟩ : ∃ w : I → ℝ, ∀ k, w k = p1 {k} := ⟨fun k => p1 {k}, fun _ => rfl⟩
  have hsum : ∀ X : Finset I, p1 X = ∑ k ∈ X, w k := by
    intro X
    refine Finset.induction_on X (by simp [z1]) ?_
    intro a s ha ih
    rw [Finset.sum_insert ha, ← ih, Finset.insert_eq,
      hadd {a} s (Finset.disjoint_singleton_left.mpr ha), hw a]
  have hpos : ∀ A, 0 ≤ p1 A := fun A =>
    le_trans (F.n12 A ∅ univ (adm_empty_mid A)) (F.l12 A ∅ univ (adm_empty_mid A))
  have hind : ∀ X : Finset I, p1 X = ∑ k, if k ∈ X then w k else 0 := by
    intro X
    rw [hsum X, ← Finset.sum_filter]
    congr 1; ext k; simp
  -- joint probabilities are the weight of the intersection
  have hinter : ∀ A B, p1 A + p1 B - p1 (A ∪ B) = p1 (A ∩ B) := by
    intro A B
    rw [hsum, hsum, hsum, hsum]
    have := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := w)
    linarith
  refine ⟨w, fun k => by rw [hw]; exact hpos {k}, by rw [← hsum univ]; exact u1, ?_⟩
  intro A B C hadm x y z
  obtain ⟨hn, h0, h1, hs, e1, e2, e3, f1, f2, f3⟩ := hM A B C hadm
  simp only [Fintype.sum_bool] at hs e1 e2 e3 f1 f2 f3
  have a1 : p1 A = ∑ k, if k ∈ A then w k else 0 := hind A
  have a2 : p2 B = ∑ k, if k ∈ B then w k else 0 := by rw [h12]; exact hind B
  have a3 : p3 C = ∑ k, if k ∈ C then w k else 0 := by rw [h32, h12]; exact hind C
  have b12 : q12 A B = ∑ k, if k ∈ A ∩ B then w k else 0 := by rw [hq12, hinter]; exact hind _
  have b23 : q23 B C = ∑ k, if k ∈ B ∩ C then w k else 0 := by rw [hq23, hinter]; exact hind _
  have b31 : q31 C A = ∑ k, if k ∈ C ∩ A then w k else 0 := by rw [hq31, hinter]; exact hind _
  -- the target sum, voter by voter
  have pt : ∀ (s : I → ℝ), (∀ k, (if (decide (k ∈ A) = x ∧ decide (k ∈ B) = y ∧ decide (k ∈ C) = z)
      then w k else 0) = s k) → (∑ k, if (decide (k ∈ A) = x ∧ decide (k ∈ B) = y ∧
      decide (k ∈ C) = z) then w k else 0) = ∑ k, s k :=
    fun s hs => Finset.sum_congr rfl (fun k _ => hs k)
  cases x <;> cases y <;> cases z
  · -- 000
    rw [h0]; symm; apply Finset.sum_eq_zero; intro k _; obtain ⟨hk1, hk2⟩ := hadm k
    by_cases ha : k ∈ A <;> by_cases hb : k ∈ B <;> by_cases hc' : k ∈ C <;>
      simp [ha, hb, hc'] at hk1 hk2 ⊢
  · -- 001
    have : e A B C false false true = p3 C - q23 B C - q31 C A := by linarith
    rw [this, a3, b23, b31, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    symm; apply pt; intro k; obtain ⟨hk1, hk2⟩ := hadm k
    by_cases ha : k ∈ A <;> by_cases hb : k ∈ B <;> by_cases hc' : k ∈ C <;>
      simp [ha, hb, hc'] at hk1 hk2 ⊢
  · -- 010
    have : e A B C false true false = p2 B - q12 A B - q23 B C := by linarith
    rw [this, a2, b12, b23, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    symm; apply pt; intro k; obtain ⟨hk1, hk2⟩ := hadm k
    by_cases ha : k ∈ A <;> by_cases hb : k ∈ B <;> by_cases hc' : k ∈ C <;>
      simp [ha, hb, hc'] at hk1 hk2 ⊢
  · -- 011
    have : e A B C false true true = q23 B C := by linarith
    rw [this, b23]
    symm; apply pt; intro k; obtain ⟨hk1, hk2⟩ := hadm k
    by_cases ha : k ∈ A <;> by_cases hb : k ∈ B <;> by_cases hc' : k ∈ C <;>
      simp [ha, hb, hc'] at hk1 hk2 ⊢
  · -- 100
    have : e A B C true false false = p1 A - q12 A B - q31 C A := by linarith
    rw [this, a1, b12, b31, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    symm; apply pt; intro k; obtain ⟨hk1, hk2⟩ := hadm k
    by_cases ha : k ∈ A <;> by_cases hb : k ∈ B <;> by_cases hc' : k ∈ C <;>
      simp [ha, hb, hc'] at hk1 hk2 ⊢
  · -- 101
    have : e A B C true false true = q31 C A := by linarith
    rw [this, b31]
    symm; apply pt; intro k; obtain ⟨hk1, hk2⟩ := hadm k
    by_cases ha : k ∈ A <;> by_cases hb : k ∈ B <;> by_cases hc' : k ∈ C <;>
      simp [ha, hb, hc'] at hk1 hk2 ⊢
  · -- 110
    have : e A B C true true false = q12 A B := by linarith
    rw [this, b12]
    symm; apply pt; intro k; obtain ⟨hk1, hk2⟩ := hadm k
    by_cases ha : k ∈ A <;> by_cases hb : k ∈ B <;> by_cases hc' : k ∈ C <;>
      simp [ha, hb, hc'] at hk1 hk2 ⊢
  · -- 111
    rw [h1]; symm; apply Finset.sum_eq_zero; intro k _; obtain ⟨hk1, hk2⟩ := hadm k
    by_cases ha : k ∈ A <;> by_cases hb : k ∈ B <;> by_cases hc' : k ∈ C <;>
      simp [ha, hb, hc'] at hk1 hk2 ⊢

end ArrowProb

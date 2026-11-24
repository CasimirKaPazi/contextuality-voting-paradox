module

public import Mathlib
public import ProbabilisticArrow
public import ArrowGeneral

@[expose] public section

/-!
# Theorem 5′ for any number of alternatives

The three-alternative case of `ArrowGeneral` from `ProbabilisticArrow` (Theorem 5), and with
`ArrowGeneral.mixture_of_base` the theorem for every number of alternatives `≥ 3`:
every empirical model on Arrow's scenario (full compatibility, unanimity) is a mixture of
dictatorships.

Translation. Name the three alternatives `a, b, c`. A ranking is determined by its comparisons
on the issues ab, bc, ca (its *bits*), and a profile by the three columns of voters with bit 1.
The lottery `e A B C x y z` of `ProbabilisticArrow` is the probability, at the profile with
columns `A B C`, of the social ranking with bits `x y z`; the marginals are computed at fixed
admissible profiles, and full compatibility shows they depend only on the relevant columns.
-/

open Finset PathPinning ArrowGeneral

namespace ArrowBase

universe u v

/-- Three named alternatives covering `β`. -/
structure Tri (β : Type u) where
  a : β
  b : β
  c : β
  hab : a ≠ b
  hac : a ≠ c
  hbc : b ≠ c
  cov : ∀ x, x = a ∨ x = b ∨ x = c

section Rankings
variable {β : Type u} [Fintype β] [DecidableEq β]

/-- The ranking p > q > r. -/
def ofTriple (p q r : β) (_hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hcov : ∀ x, x = p ∨ x = q ∨ x = r) : Rk β :=
  ⟨fun u v => decide ((u = p ∧ v ≠ p) ∨ (u = q ∧ v = r)), by
    unfold IsRank
    refine ⟨fun u => ?_, fun u w z h1 h2 => ?_, fun u w huw => ?_⟩
    · simp only [decide_eq_false_iff_not]
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact h2 h1
      · exact hqr (h1.symm.trans h2)
    · simp only [decide_eq_true_eq] at h1 h2 ⊢
      rcases h1 with ⟨hu, hw⟩ | ⟨hu, hw⟩
      · refine Or.inl ⟨hu, fun hz => ?_⟩
        rcases h2 with ⟨_, hz'⟩ | ⟨_, hz'⟩
        · exact hz' hz
        · exact hpr (hz.symm.trans hz')
      · rcases h2 with ⟨hw', _⟩ | ⟨hw', _⟩
        · exact absurd (hw.symm.trans hw') (Ne.symm hpr)
        · exact absurd (hw.symm.trans hw') (Ne.symm hqr)
    · simp only [decide_eq_true_eq]
      by_cases hu : u = p
      · exact Or.inl (Or.inl ⟨hu, fun hw => huw (hu.trans hw.symm)⟩)
      by_cases hw : w = p
      · exact Or.inr (Or.inl ⟨hw, hu⟩)
      rcases hcov u with h | h | h
      · exact absurd h hu
      · rcases hcov w with h' | h' | h'
        · exact absurd h' hw
        · exact absurd (h.trans h'.symm) huw
        · exact Or.inl (Or.inr ⟨h, h'⟩)
      · rcases hcov w with h' | h' | h'
        · exact absurd h' hw
        · exact Or.inr (Or.inr ⟨h', h⟩)
        · exact absurd (h.trans h'.symm) huw⟩

variable (T : Tri β)

/-- The bits of a ranking on the issues ab, bc, ca. -/
def bitsOf (σ : Rk β) : Bool × Bool × Bool := (σ.1 T.a T.b, σ.1 T.b T.c, σ.1 T.c T.a)

lemma rev (σ : Rk β) {x y : β} (h : x ≠ y) : σ.1 y x = !σ.1 x y := by
  rcases PathPinning.total σ h with h' | h'
  · rw [PathPinning.asymm σ h', h']; rfl
  · rw [h', PathPinning.asymm σ h']; rfl

/-- A ranking is determined by its bits. -/
lemma bits_inj {σ σ' : Rk β} (h : bitsOf T σ = bitsOf T σ') : σ = σ' := by
  simp only [bitsOf, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  apply Subtype.ext; funext u v
  rcases T.cov u with rfl | rfl | rfl <;> rcases T.cov v with rfl | rfl | rfl
  · rw [PathPinning.irrefl, PathPinning.irrefl]
  · exact h1
  · rw [rev σ (Ne.symm T.hac), rev σ' (Ne.symm T.hac), h3]
  · rw [rev σ T.hab, rev σ' T.hab, h1]
  · rw [PathPinning.irrefl, PathPinning.irrefl]
  · exact h2
  · exact h3
  · rw [rev σ T.hbc, rev σ' T.hbc, h2]
  · rw [PathPinning.irrefl, PathPinning.irrefl]

/-- No ranking has all three bits equal. -/
lemma bits_adm (σ : Rk β) :
    ¬ (σ.1 T.a T.b = true ∧ σ.1 T.b T.c = true ∧ σ.1 T.c T.a = true) ∧
    ¬ (σ.1 T.a T.b = false ∧ σ.1 T.b T.c = false ∧ σ.1 T.c T.a = false) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have := PathPinning.trans' σ h1 h2
    rw [PathPinning.asymm σ this] at h3; exact absurd h3 (by simp)
  · rintro ⟨h1, h2, h3⟩
    have h1' : σ.1 T.b T.a = true := by rw [rev σ T.hab, h1]; rfl
    have h3' : σ.1 T.a T.c = true := by rw [rev σ (Ne.symm T.hac), h3]; rfl
    have := PathPinning.trans' σ h1' h3'
    rw [h2] at this; exact absurd this (by simp)

/-- The ranking with given bits (any ranking if the bits are all equal). -/
def mk (x y z : Bool) : Rk β :=
  have c1 : ∀ w, w = T.a ∨ w = T.b ∨ w = T.c := T.cov
  match x, y, z with
  | true, true, false => ofTriple T.a T.b T.c T.hab T.hac T.hbc c1
  | true, false, false => ofTriple T.a T.c T.b T.hac T.hab (Ne.symm T.hbc)
      (fun w => by rcases T.cov w with h | h | h <;> simp [h])
  | true, false, true => ofTriple T.c T.a T.b (Ne.symm T.hac) (Ne.symm T.hbc) T.hab
      (fun w => by rcases T.cov w with h | h | h <;> simp [h])
  | false, true, true => ofTriple T.b T.c T.a T.hbc (Ne.symm T.hab) (Ne.symm T.hac)
      (fun w => by rcases T.cov w with h | h | h <;> simp [h])
  | false, true, false => ofTriple T.b T.a T.c (Ne.symm T.hab) T.hbc T.hac
      (fun w => by rcases T.cov w with h | h | h <;> simp [h])
  | false, false, true => ofTriple T.c T.b T.a (Ne.symm T.hbc) (Ne.symm T.hac) (Ne.symm T.hab)
      (fun w => by rcases T.cov w with h | h | h <;> simp [h])
  | _, _, _ => ofTriple T.a T.b T.c T.hab T.hac T.hbc c1

lemma mk_bits (x y z : Bool) (h1 : ¬ (x = true ∧ y = true ∧ z = true))
    (h2 : ¬ (x = false ∧ y = false ∧ z = false)) : bitsOf T (mk T x y z) = (x, y, z) := by
  have hab := T.hab; have hac := T.hac; have hbc := T.hbc
  cases x <;> cases y <;> cases z <;> simp at h1 h2 <;>
    simp [bitsOf, mk, ofTriple, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]

/-- Sums over rankings, split by bits. -/
lemma sum_bits (f : Rk β → ℝ) (Q : Bool → Bool → Bool → Prop) [∀ x y z, Decidable (Q x y z)] :
    ∑ σ ∈ univ.filter (fun σ => Q (σ.1 T.a T.b) (σ.1 T.b T.c) (σ.1 T.c T.a)), f σ =
      ∑ x, ∑ y, ∑ z, if Q x y z then
        ∑ σ ∈ univ.filter (fun σ => bitsOf T σ = (x, y, z)), f σ else 0 := by
  rw [Finset.sum_filter]
  rw [← Finset.sum_fiberwise univ (bitsOf T)
    (fun σ => if Q (σ.1 T.a T.b) (σ.1 T.b T.c) (σ.1 T.c T.a) then f σ else 0)]
  simp_rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ =>
    Finset.sum_congr rfl (fun z _ => ?_)))
  split_ifs with hQ
  · apply Finset.sum_congr rfl
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, bitsOf, Prod.mk.injEq] at hσ
    simp only [hσ.1, hσ.2.1, hσ.2.2, hQ, ↓reduceIte]
  · apply Finset.sum_eq_zero
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, bitsOf, Prod.mk.injEq] at hσ
    simp only [hσ.1, hσ.2.1, hσ.2.2, hQ, ↓reduceIte]

end Rankings

section Base
variable {ι : Type v} [Fintype ι] [DecidableEq ι] {β : Type u} [Fintype β] [DecidableEq β]
variable (T : Tri β)

/-- The profile with columns `A B C` on the issues ab, bc, ca. -/
def prof (A B C : Finset ι) : ι → Rk β :=
  fun k => mk T (decide (k ∈ A)) (decide (k ∈ B)) (decide (k ∈ C))

omit [Fintype ι] in
lemma prof_bits {A B C : Finset ι} (k : ι) (h1 : ¬ (k ∈ A ∧ k ∈ B ∧ k ∈ C))
    (h2 : ¬ (k ∉ A ∧ k ∉ B ∧ k ∉ C)) :
    (prof T A B C k).1 T.a T.b = decide (k ∈ A) ∧ (prof T A B C k).1 T.b T.c = decide (k ∈ B) ∧
      (prof T A B C k).1 T.c T.a = decide (k ∈ C) := by
  have := mk_bits T (decide (k ∈ A)) (decide (k ∈ B)) (decide (k ∈ C))
    (by simpa using h1) (by simpa using h2)
  simp only [bitsOf, Prod.mk.injEq] at this
  exact this

omit [Fintype ι] [DecidableEq ι] in
lemma prob_split (μ : (ι → Rk β) → Rk β → ℝ) (hM : Model μ) (π : ι → Rk β) (x y : β)
    (hxy : x ≠ y) : prob μ π (fun σ => σ.1 x y) + prob μ π (fun σ => σ.1 y x) = 1 := by
  have hf : univ.filter (fun σ : Rk β => σ.1 y x = true) =
      univ.filter (fun σ : Rk β => ¬ σ.1 x y = true) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [rev σ hxy]; cases σ.1 x y <;> simp
  simp only [prob]
  rw [hf, Finset.sum_filter_add_sum_filter_not]
  exact hM.total π

/-- **Theorem 5 in the general framework**: three alternatives. -/
theorem base3 (T : Tri β) (μ : (ι → Rk β) → Rk β → ℝ) (hM : Model μ) : IsMixture μ := by
  have hab := T.hab; have hac := T.hac; have hbc := T.hbc
  let e : Finset ι → Finset ι → Finset ι → Bool → Bool → Bool → ℝ := fun A B C x y z =>
    ∑ σ ∈ univ.filter (fun σ => bitsOf T σ = (x, y, z)), μ (prof T A B C) σ
  let p1 : Finset ι → ℝ := fun A => prob μ (prof T A ∅ univ) (fun σ => σ.1 T.a T.b)
  let p2 : Finset ι → ℝ := fun B => prob μ (prof T univ B ∅) (fun σ => σ.1 T.b T.c)
  let p3 : Finset ι → ℝ := fun C => prob μ (prof T ∅ univ C) (fun σ => σ.1 T.c T.a)
  let q12 : Finset ι → Finset ι → ℝ := fun A B =>
    prob μ (prof T A B (A ∩ B)ᶜ) (fun σ => σ.1 T.a T.b && σ.1 T.b T.c)
  let q23 : Finset ι → Finset ι → ℝ := fun B C =>
    prob μ (prof T (B ∩ C)ᶜ B C) (fun σ => σ.1 T.b T.c && σ.1 T.c T.a)
  let q31 : Finset ι → Finset ι → ℝ := fun C A =>
    prob μ (prof T A (C ∩ A)ᶜ C) (fun σ => σ.1 T.c T.a && σ.1 T.a T.b)
  -- admissibility of the auxiliary profiles
  have admA : ∀ A : Finset ι, ArrowProb.Adm A ∅ univ := fun A => by intro k; simp
  have admB : ∀ B : Finset ι, ArrowProb.Adm univ B ∅ := fun B => by intro k; simp
  have admC : ∀ C : Finset ι, ArrowProb.Adm ∅ univ C := fun C => by intro k; simp
  -- probabilities of events on one or two issues depend only on their columns
  have same1 : ∀ (A B C A' B' C' : Finset ι), ArrowProb.Adm A B C → ArrowProb.Adm A' B' C' →
      ∀ (i j : β) (hi : (∀ k, (prof T A B C k).1 i j = (prof T A' B' C' k).1 i j)),
      prob μ (prof T A B C) (fun σ => σ.1 i j) = prob μ (prof T A' B' C') (fun σ => σ.1 i j) := by
    intro A B C A' B' C' _ _ i j hi
    apply hM.compat {(i, j)} _ (det_rel (Finset.mem_singleton_self _))
    intro k p hp
    rw [Finset.mem_singleton] at hp; subst hp
    exact hi k
  have same2 : ∀ (π π' : ι → Rk β) (i j l m : β),
      (∀ k, (π k).1 i j = (π' k).1 i j) → (∀ k, (π k).1 l m = (π' k).1 l m) →
      prob μ π (fun σ => σ.1 i j && σ.1 l m) = prob μ π' (fun σ => σ.1 i j && σ.1 l m) := by
    intro π π' i j l m h1 h2
    apply hM.compat {(i, j), (l, m)}
    · intro σ σ' hag
      have e1 : σ.1 i j = σ'.1 i j := hag (i, j) (by simp)
      have e2 : σ.1 l m = σ'.1 l m := hag (l, m) (by simp)
      show (σ.1 i j && σ.1 l m) = (σ'.1 i j && σ'.1 l m)
      rw [e1, e2]
    · intro k p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact h1 k
      · exact h2 k
  have hModel : ArrowProb.Model e p1 p2 p3 q12 q23 q31 := by
    intro A B C hadm
    have bitsABC := fun k => prof_bits T (A := A) (B := B) (C := C) k (hadm k).1 (hadm k).2
    -- the eight values of e, as sums over all rankings with given bits
    have hsum : ∀ (Q : Bool → Bool → Bool → Prop) [∀ x y z, Decidable (Q x y z)],
        ∑ σ ∈ univ.filter (fun σ => Q (σ.1 T.a T.b) (σ.1 T.b T.c) (σ.1 T.c T.a)),
          μ (prof T A B C) σ = ∑ x, ∑ y, ∑ z, if Q x y z then e A B C x y z else 0 :=
      fun Q _ => sum_bits T (μ (prof T A B C)) Q
    refine ⟨fun x y z => Finset.sum_nonneg (fun σ _ => hM.nonneg _ σ), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply Finset.sum_eq_zero; intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, bitsOf, Prod.mk.injEq] at hσ
      exact absurd hσ (bits_adm T σ).2
    · apply Finset.sum_eq_zero; intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, bitsOf, Prod.mk.injEq] at hσ
      exact absurd hσ (bits_adm T σ).1
    · have := hsum (fun _ _ _ => True)
      simp only [↓reduceIte] at this
      rw [← this, Finset.filter_true_of_mem (fun _ _ => trivial)]
      exact hM.total _
    · -- p1
      have h := hsum (fun x _ _ => x = true)
      simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, add_zero] at h ⊢
      rw [← h]
      show prob μ (prof T A ∅ univ) (fun σ => σ.1 T.a T.b) = prob μ (prof T A B C) (fun σ => σ.1 T.a T.b)
      apply same1 _ _ _ _ _ _ (admA A) hadm
      intro k
      rw [(prof_bits T k ((admA A) k).1 ((admA A) k).2).1, (bitsABC k).1]
    · -- p2
      have h := hsum (fun _ y _ => y = true)
      simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, add_zero] at h ⊢
      rw [← h]
      show prob μ (prof T univ B ∅) (fun σ => σ.1 T.b T.c) = prob μ (prof T A B C) (fun σ => σ.1 T.b T.c)
      apply same1 _ _ _ _ _ _ (admB B) hadm
      intro k
      rw [(prof_bits T k ((admB B) k).1 ((admB B) k).2).2.1, (bitsABC k).2.1]
    · -- p3
      have h := hsum (fun _ _ z => z = true)
      simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, add_zero] at h ⊢
      rw [← h]
      show prob μ (prof T ∅ univ C) (fun σ => σ.1 T.c T.a) = prob μ (prof T A B C) (fun σ => σ.1 T.c T.a)
      apply same1 _ _ _ _ _ _ (admC C) hadm
      intro k
      rw [(prof_bits T k ((admC C) k).1 ((admC C) k).2).2.2, (bitsABC k).2.2]
    · -- q12
      have h := hsum (fun x y _ => x = true ∧ y = true)
      simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, and_true, and_false, add_zero] at h ⊢
      have hadm' : ArrowProb.Adm A B (A ∩ B)ᶜ := ArrowProb.adm_Wstar A B
      have e' : prob μ (prof T A B C) (fun σ => σ.1 T.a T.b && σ.1 T.b T.c) =
          ∑ σ ∈ univ.filter (fun σ => σ.1 T.a T.b = true ∧ σ.1 T.b T.c = true), μ (prof T A B C) σ := by
        unfold prob; apply Finset.sum_congr _ (fun _ _ => rfl); ext σ; simp
      rw [← h, ← e']
      show prob μ (prof T A B (A ∩ B)ᶜ) _ = _
      apply same2
      · intro k; rw [(prof_bits T k (hadm' k).1 (hadm' k).2).1, (bitsABC k).1]
      · intro k; rw [(prof_bits T k (hadm' k).1 (hadm' k).2).2.1, (bitsABC k).2.1]
    · -- q23
      have h := hsum (fun _ y z => y = true ∧ z = true)
      simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, and_true, and_false, add_zero] at h ⊢
      have hadm' : ArrowProb.Adm (B ∩ C)ᶜ B C := (ArrowProb.adm_Wstar B C).rot.rot
      have e' : prob μ (prof T A B C) (fun σ => σ.1 T.b T.c && σ.1 T.c T.a) =
          ∑ σ ∈ univ.filter (fun σ => σ.1 T.b T.c = true ∧ σ.1 T.c T.a = true), μ (prof T A B C) σ := by
        unfold prob; apply Finset.sum_congr _ (fun _ _ => rfl); ext σ; simp
      rw [← h, ← e']
      show prob μ (prof T (B ∩ C)ᶜ B C) _ = _
      apply same2
      · intro k; rw [(prof_bits T k (hadm' k).1 (hadm' k).2).2.1, (bitsABC k).2.1]
      · intro k; rw [(prof_bits T k (hadm' k).1 (hadm' k).2).2.2, (bitsABC k).2.2]
    · -- q31
      have h := hsum (fun x _ z => z = true ∧ x = true)
      simp only [Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true, true_and, false_and, add_zero] at h ⊢
      have hadm' : ArrowProb.Adm A (C ∩ A)ᶜ C := (ArrowProb.adm_Wstar C A).rot
      have e' : prob μ (prof T A B C) (fun σ => σ.1 T.c T.a && σ.1 T.a T.b) =
          ∑ σ ∈ univ.filter (fun σ => σ.1 T.c T.a = true ∧ σ.1 T.a T.b = true), μ (prof T A B C) σ := by
        unfold prob; apply Finset.sum_congr _ (fun _ _ => rfl); ext σ; simp
      rw [← h, ← e']
      show prob μ (prof T A (C ∩ A)ᶜ C) _ = _
      apply same2
      · intro k; rw [(prof_bits T k (hadm' k).1 (hadm' k).2).2.2, (bitsABC k).2.2]
      · intro k; rw [(prof_bits T k (hadm' k).1 (hadm' k).2).1, (bitsABC k).1]
  -- unanimity
  have un : ∀ (π : ι → Rk β) (x y : β), x ≠ y →
      (∀ k, (π k).1 x y = true) → prob μ π (fun σ => σ.1 x y) = 1 ∧ prob μ π (fun σ => σ.1 y x) = 0 := by
    intro π x y hxy h
    have h1 := hM.unan π x y h
    have h2 := prob_split μ hM π x y hxy
    exact ⟨h1, by linarith⟩
  have u1 : p1 univ = 1 :=
    (un (prof T univ ∅ univ) T.a T.b hab (fun k => by rw [(prof_bits T k ((admA univ) k).1 ((admA univ) k).2).1]; simp)).1
  have u2 : p2 univ = 1 :=
    (un (prof T univ univ ∅) T.b T.c hbc (fun k => by rw [(prof_bits T k ((admB univ) k).1 ((admB univ) k).2).2.1]; simp)).1
  have u3 : p3 univ = 1 :=
    (un (prof T ∅ univ univ) T.c T.a (Ne.symm hac) (fun k => by
      rw [(prof_bits T k ((admC univ) k).1 ((admC univ) k).2).2.2]; simp)).1
  have z1 : p1 ∅ = 0 := by
    have := (un (prof T ∅ ∅ univ) T.b T.a (Ne.symm hab) (fun k => by
      rw [rev _ hab, (prof_bits T k ((admA ∅) k).1 ((admA ∅) k).2).1]; simp)).2
    exact this
  have z2 : p2 ∅ = 0 := by
    have := (un (prof T univ ∅ ∅) T.c T.b (Ne.symm hbc) (fun k => by
      rw [rev _ hbc, (prof_bits T k ((admB ∅) k).1 ((admB ∅) k).2).2.1]; simp)).2
    exact this
  have z3 : p3 ∅ = 0 := by
    have := (un (prof T ∅ univ ∅) T.a T.c hac (fun k => by
      rw [rev _ (Ne.symm hac), (prof_bits T k ((admC ∅) k).1 ((admC ∅) k).2).2.2]; simp)).2
    exact this
  obtain ⟨w, hw0, hw1, hmix⟩ :=
    ArrowProb.mixture_of_dictatorships e p1 p2 p3 q12 q23 q31 hModel u1 u2 u3 z1 z2 z3
  refine ⟨w, hw0, hw1, fun π σ => ?_⟩
  -- the columns of π
  let A := univ.filter (fun k => (π k).1 T.a T.b = true)
  let B := univ.filter (fun k => (π k).1 T.b T.c = true)
  let C := univ.filter (fun k => (π k).1 T.c T.a = true)
  have hadm : ArrowProb.Adm A B C := by
    intro k
    have := bits_adm T (π k)
    simp only [A, B, C, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true]
    exact this
  have hprof : prof T A B C = π := by
    funext k
    apply bits_inj T
    obtain ⟨h1, h2, h3⟩ := prof_bits T (A := A) (B := B) (C := C) k (hadm k).1 (hadm k).2
    simp only [bitsOf, h1, h2, h3, A, B, C, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.decide_eq_true]
  have hfiber : univ.filter (fun τ => bitsOf T τ = bitsOf T σ) = {σ} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨bits_inj T, fun h => by rw [h]⟩
  have key := hmix A B C hadm (σ.1 T.a T.b) (σ.1 T.b T.c) (σ.1 T.c T.a)
  have hleft : e A B C (σ.1 T.a T.b) (σ.1 T.b T.c) (σ.1 T.c T.a) = μ π σ := by
    show ∑ τ ∈ univ.filter (fun τ => bitsOf T τ = bitsOf T σ), μ (prof T A B C) τ = μ π σ
    rw [hfiber, Finset.sum_singleton, hprof]
  rw [← hleft, key, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  have hiff : (decide (k ∈ A) = σ.1 T.a T.b ∧ decide (k ∈ B) = σ.1 T.b T.c ∧
      decide (k ∈ C) = σ.1 T.c T.a) ↔ π k = σ := by
    simp only [A, B, C, Finset.mem_filter, Finset.mem_univ, true_and, Bool.decide_eq_true]
    constructor
    · intro h; apply bits_inj T; simp only [bitsOf, Prod.mk.injEq]; exact h
    · intro h; rw [h]; exact ⟨rfl, rfl, rfl⟩
  simp only [hiff]

end Base

/-- **Theorem 5′.** For any finite set of voters and any number `≥ 3` of alternatives, every
empirical model on Arrow's scenario is a mixture of dictatorships. -/
theorem theorem5' {ι : Type v} [Fintype ι] [DecidableEq ι] (α : Type u) [Fintype α]
    [DecidableEq α] (hα : 3 ≤ Fintype.card α) (μ : (ι → Rk α) → Rk α → ℝ) (hM : Model μ) :
    IsMixture μ := by
  refine mixture_of_base (fun β _ _ hβ μ hM => ?_) α hα μ hM
  have h3 : (univ : Finset β).card = 3 := by rw [Finset.card_univ]; exact hβ
  obtain ⟨x, y, z, hxy, hxz, hyz, huniv⟩ := Finset.card_eq_three.mp h3
  have hcov : ∀ w : β, w = x ∨ w = y ∨ w = z := by
    intro w
    have : w ∈ (univ : Finset β) := Finset.mem_univ w
    rw [huniv] at this
    simpa using this
  exact base3 ⟨x, y, z, hxy, hxz, hyz, hcov⟩ μ hM

end ArrowBase

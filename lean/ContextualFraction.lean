/-
  Proposition 5 of *The Global Form* (`notes/global-form.md`, Section 7):
  for three alternatives and any finite set of voters, with Gibbard's 1977
  theorem as a hypothesis,

  * the SD-SP lotteries are exactly the mixtures of the deterministic SP
    rules and the random top twos, one per voter (`prop5_decomp`,
    `model_of_decomp`);
  * the degree of each voter does not depend on the context
    (`deg_indep`);
  * a lottery rule is non-contextual exactly when no degree is negative
    (`nc_iff`);
  * its contextual fraction is CF = 2 · Σ_i max(0, −deg_i) (`cf`).

  Encoding. A profile gives each voter one of the six rankings of
  `GlobalFormLottery` (`Prof`); a rule gives a lottery on the three outcomes
  at each profile (`LRule`, `Lot`). A rule is SD-SP when every voter's slice,
  the one-voter rule obtained by fixing the others, is SD-SP (`SDSPn`); the
  degree of voter i at profile π is the degree of that slice (`degAt`). A
  model is an SD-SP lottery rule (`Model`): by Proposition 1 of
  *Gibbard–Satterthwaite as a Scenario* these are the empirical models of
  that scenario. Non-contextual (`NC`) means a mixture of deterministic SP
  rules, the global sections; the mixtures are built as a cone
  (`NCc N t`: N is a non-negative combination of deterministic SP rules with
  total weight t). The contextual fraction is the least weight of the second
  part in a decomposition L = (1 − λ) N + λ M with N non-contextual and M a
  model (Abramsky, Barbosa and Mansfield).

  Gibbard's theorem enters as `Gibbard1977`: every SD-SP lottery rule is a
  finite mixture of SD-SP lottery rules, each unilateral (it depends on one
  voter's ballot) or duple (it puts all probability on two alternatives).
  This includes, as Gibbard's theorem does, that the components are
  themselves SD-SP; `GSCorollary.Gibbard1977` omits that part, which its
  corollary does not need.

  The proof is the note's.
  * Duples are mixtures of deterministic SP duples (`nc_duple`): the
    probability of a depends monotonically on the ballots through which of a
    and b each voter prefers (`mono_of_duple`), and a monotone function into
    [0, 1] is a mixture of monotone yes-or-no functions (`nc_dupR`, by
    induction on the number of values strictly between 0 and 1, splitting
    off the least of them).
  * Grouping the unilateral components by voter gives one one-voter SD-SP
    rule per voter; Proposition 4 decomposes it.
  * The lower bound (`cf_lower`): degrees of non-contextual rules are
    non-negative (`NCc.deg_nonneg`), and those of any model sum to at least
    −1/2 over the voters with negative degree (`model_bound`), since each
    component is negative for at most one voter, by at most 1/2.
-/

module

public import Mathlib
public import GlobalFormLottery

@[expose] public section

open Finset GlobalFormLottery

namespace ContextualFraction

/-! ### One-voter facts -/

lemma deg_add (f g : Rule) : deg (fun r x => f r x + g r x) = deg f + deg g := by
  unfold deg; ring

lemma deg_smul (c : ℝ) (f : Rule) : deg (fun r x => c * f r x) = c * deg f := by
  unfold deg; ring

lemma deg_zero : deg (fun _ _ => 0) = 0 := by
  unfold deg; ring

lemma deg_sum {J : Type*} (s : Finset J) (g : J → Rule) :
    deg (fun r x => ∑ j ∈ s, g j r x) = ∑ j ∈ s, deg (g j) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [sum_empty]
    exact deg_zero
  · intro a s ha ih
    simp only [sum_insert ha]
    rw [deg_add, ih]

lemma deg_const (f : Rule) (h : ∀ r, f r = f 0) : deg f = 0 := by
  unfold deg
  rw [h 1, h 2, h 3, h 4, h 5]
  ring

lemma sdsp_const (f : Rule) (h : ∀ r, f r = f 0) : SDSP f := fun r r' => by
  rw [h r, h r']
  exact ⟨le_refl _, le_refl _⟩

lemma sdsp_add {f g : Rule} (hf : SDSP f) (hg : SDSP g) : SDSP (fun r x => f r x + g r x) :=
  fun r r' => by
    beta_reduce
    exact ⟨by linarith [(hf r r').1, (hg r r').1], by linarith [(hf r r').2, (hg r r').2]⟩

lemma sdsp_smul {c : ℝ} (hc : 0 ≤ c) {f : Rule} (hf : SDSP f) : SDSP (fun r x => c * f r x) :=
  fun r r' => by
    beta_reduce
    refine ⟨mul_le_mul_of_nonneg_left (hf r r').1 hc, ?_⟩
    rw [← mul_add, ← mul_add]
    exact mul_le_mul_of_nonneg_left (hf r r').2 hc

lemma lottery_pt (g : Fin 6 → Fin 3) : Lottery (fun r => pt (g r)) := by
  intro r
  refine ⟨fun x => by show 0 ≤ pt (g r) x; unfold pt; split_ifs <;> norm_num, ?_⟩
  show pt (g r) 0 + pt (g r) 1 + pt (g r) 2 = 1
  generalize g r = y
  fin_cases y <;> norm_num [pt]

/-- A deterministic SP rule for one voter has non-negative degree: its
    decomposition gives no weight to the random top two. -/
lemma det_deg_nonneg (g : Fin 6 → Fin 3) (hS : SDSP (fun r => pt (g r))) :
    0 ≤ deg (fun r => pt (g r)) := by
  obtain ⟨w, hw, -, hf, -⟩ := decomp (lottery_pt g) hS
  have e0 := congrFun (congrFun hf 0) 0
  have e1 := congrFun (congrFun hf 0) 1
  norm_num [mix, pt, top, sec, bab, bbc, bac] at e0 e1
  have h7 : w 7 = 0 := by
    have := hw 0; have := hw 1; have := hw 3; have := hw 4; have := hw 5; have := hw 6
    have := hw 7
    generalize g 0 = y at e0 e1
    fin_cases y <;> norm_num at e0 e1 <;> linarith
  rw [hf, deg_mix, h7]
  linarith [hw 6]

/-- A one-voter SD-SP lottery that never gives z any probability has degree 0. -/
lemma duple_deg {f : Rule} (hL : Lottery f) (hS : SDSP f) (z : Fin 3) (hz : ∀ r, f r z = 0) :
    deg f = 0 := by
  obtain ⟨w, hw, -, hf, -⟩ := decomp hL hS
  have := hw 0; have := hw 1; have := hw 2; have := hw 3; have := hw 4; have := hw 5
  have := hw 6; have := hw 7
  rw [hf, deg_mix]
  fin_cases z
  · have e := hz 0
    rw [hf] at e
    norm_num [mix, pt, top, sec, bab, bbc, bac] at e
    linarith
  · have e := hz 4
    rw [hf] at e
    norm_num [mix, pt, top, sec, bab, bbc, bac] at e
    linarith
  · have e := hz 2
    rw [hf] at e
    norm_num [mix, pt, top, sec, bab, bbc, bac] at e
    linarith

lemma exists_third (a b : Fin 3) : ∃ z, z ≠ a ∧ z ≠ b := by
  fin_cases a <;> fin_cases b <;> decide

/-- The deterministic outcomes of the seven deterministic vertices of
    Proposition 4 (the last entry, unused, repeats the dictatorship). -/
def vtx : Fin 8 → Fin 6 → Fin 3 := ![fun _ => 0, fun _ => 1, fun _ => 2, bab, bbc, bac, top, top]

lemma vtx_sdsp (l : Fin 8) : SDSP (fun r => pt (vtx l r)) := by
  intro r r'
  fin_cases l <;> fin_cases r <;> fin_cases r' <;> norm_num [pt, vtx, top, sec, bab, bbc, bac]

lemma topTwo_sdsp : SDSP (fun r x => (pt (top r) x + pt (sec r) x) / 2) := by
  intro r r'
  fin_cases r <;> fin_cases r' <;> norm_num [pt, top, sec]

lemma mix_split (w : Fin 8 → ℝ) (r : Fin 6) (x : Fin 3) :
    mix w r x = ∑ l ∈ univ.erase 7, w l * pt (vtx l r) x +
      w 7 * ((pt (top r) x + pt (sec r) x) / 2) := by
  rw [sum_erase_eq_sub (mem_univ _), Fin.sum_univ_eight]
  have v0 : vtx 0 r = 0 := rfl
  have v1 : vtx 1 r = 1 := rfl
  have v2 : vtx 2 r = 2 := rfl
  have v3 : vtx 3 r = bab r := rfl
  have v4 : vtx 4 r = bbc r := rfl
  have v5 : vtx 5 r = bac r := rfl
  have v6 : vtx 6 r = top r := rfl
  have v7 : vtx 7 r = top r := rfl
  rw [v0, v1, v2, v3, v4, v5, v6, v7]
  unfold mix
  ring

lemma max_two (d : ℝ) : max 0 (-2 * d) = 2 * max 0 (-d) := by
  rcases le_total d 0 with h | h
  · rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    ring
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    ring

/-! ### Rules on profiles -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A profile: one of the six rankings for each voter. -/
abbrev Prof (ι : Type*) := ι → Fin 6

/-- A lottery rule on profiles. -/
abbrev LRule (ι : Type*) := Prof ι → Fin 3 → ℝ

/-- Voter i's slice at π: the one-voter rule with the others fixed. -/
def slice (L : LRule ι) (π : Prof ι) (i : ι) : Rule := fun r => L (Function.update π i r)

omit [Fintype ι] [DecidableEq ι] in
/-- A lottery at every profile. -/
def Lot (L : LRule ι) : Prop := ∀ π, (∀ x, 0 ≤ L π x) ∧ L π 0 + L π 1 + L π 2 = 1

omit [Fintype ι] in
/-- SD-SP: every slice is SD-SP. -/
def SDSPn (L : LRule ι) : Prop := ∀ π i, SDSP (slice L π i)

omit [Fintype ι] in
/-- An SD-SP lottery rule: an empirical model of the Gibbard–Satterthwaite scenario. -/
def Model (L : LRule ι) : Prop := Lot L ∧ SDSPn L

omit [Fintype ι] in
/-- The degree of voter i at the profile π. -/
noncomputable def degAt (L : LRule ι) (π : Prof ι) (i : ι) : ℝ := deg (slice L π i)

omit [Fintype ι] in
lemma lottery_slice {L : LRule ι} (hL : Lot L) (π : Prof ι) (i : ι) : Lottery (slice L π i) :=
  fun r => hL (Function.update π i r)

omit [Fintype ι] in
/-- A deterministic SP rule. -/
def DetSP (d : Prof ι → Fin 3) : Prop := SDSPn (fun π x => pt (d π) x)

omit [Fintype ι] in
/-- The random top two of voter i. -/
noncomputable def T2 (i : ι) : LRule ι := fun π x => (pt (top (π i)) x + pt (sec (π i)) x) / 2

omit [Fintype ι] [DecidableEq ι] in
/-- The rule depends on one voter's ballot only. -/
def Unilateral (K : LRule ι) : Prop := ∃ k, ∀ π π' : Prof ι, π k = π' k → K π = K π'

omit [Fintype ι] [DecidableEq ι] in
/-- The rule puts all probability on two fixed alternatives. -/
def Duple (K : LRule ι) : Prop := ∃ a b : Fin 3, ∀ π x, x ≠ a → x ≠ b → K π x = 0

variable (ι) in
/-- Gibbard (1977), as a hypothesis: every SD-SP lottery rule is a finite
    mixture of SD-SP lottery rules, each unilateral or duple. -/
def Gibbard1977 : Prop :=
  ∀ L : LRule ι, Model L → ∃ (n : ℕ) (w : Fin n → ℝ) (K : Fin n → LRule ι),
    (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ (∀ j, Model (K j)) ∧
      (∀ j, Unilateral (K j) ∨ Duple (K j)) ∧ ∀ π x, L π x = ∑ j, w j * K j π x

omit [Fintype ι] in
lemma slice_const_of_ne {K : LRule ι} {k : ι} (hK : ∀ π π' : Prof ι, π k = π' k → K π = K π')
    {i : ι} (hik : i ≠ k) (π : Prof ι) : ∀ r, slice K π i r = slice K π i 0 := fun r =>
  hK _ _ (by rw [Function.update_of_ne hik.symm, Function.update_of_ne hik.symm])

omit [Fintype ι] in
lemma degAt_sum {J : Type*} (s : Finset J) (w : J → ℝ) (K : J → LRule ι) (π : Prof ι) (i : ι) :
    degAt (fun π x => ∑ j ∈ s, w j * K j π x) π i = ∑ j ∈ s, w j * degAt (K j) π i := by
  unfold degAt slice
  rw [deg_sum]
  exact sum_congr rfl fun j _ => deg_smul _ _

omit [Fintype ι] in
lemma t2_model (i : ι) : Model (T2 i) := by
  refine ⟨fun π => ⟨fun x => ?_, ?_⟩, fun π k => ?_⟩
  · unfold T2 pt
    split_ifs <;> norm_num
  · unfold T2
    generalize π i = r
    fin_cases r <;> norm_num [pt, top, sec]
  · by_cases hk : k = i
    · subst hk
      have : slice (T2 k) π k = fun r x => (pt (top r) x + pt (sec r) x) / 2 := by
        funext r x
        simp [slice, T2]
      rw [this]
      exact topTwo_sdsp
    · refine sdsp_const _ fun r => ?_
      funext x
      simp only [slice, T2]
      rw [Function.update_of_ne (Ne.symm hk), Function.update_of_ne (Ne.symm hk)]

/-! ### The cone of non-contextual rules -/

omit [Fintype ι] in
/-- `NCc N t`: N is a non-negative combination of deterministic SP rules with
    total weight t. -/
inductive NCc : LRule ι → ℝ → Prop
  | zero : NCc (fun _ _ => 0) 0
  | det (d : Prof ι → Fin 3) (c : ℝ) : DetSP d → 0 ≤ c → NCc (fun π x => c * pt (d π) x) c
  | add {N M : LRule ι} {s t : ℝ} : NCc N s → NCc M t → NCc (fun π x => N π x + M π x) (s + t)

omit [Fintype ι] in
/-- Non-contextual: a mixture of deterministic SP rules. -/
def NC (N : LRule ι) : Prop := NCc N 1

omit [Fintype ι] in
lemma NCc.congr {N N' : LRule ι} {t t' : ℝ} (h : NCc N t) (he : ∀ π x, N π x = N' π x)
    (ht : t = t') : NCc N' t' := by
  have : N = N' := funext fun π => funext (he π)
  subst this ht
  exact h

omit [Fintype ι] in
lemma NCc.smul {N : LRule ι} {t : ℝ} (h : NCc N t) {c : ℝ} (hc : 0 ≤ c) :
    NCc (fun π x => c * N π x) (c * t) := by
  induction h with
  | zero => exact NCc.zero.congr (fun _ _ => by beta_reduce; ring) (by ring)
  | det d c' hd hc' =>
    exact (NCc.det d (c * c') hd (mul_nonneg hc hc')).congr (fun _ _ => by beta_reduce; ring) rfl
  | add _ _ ih1 ih2 =>
    exact (NCc.add ih1 ih2).congr (fun _ _ => by beta_reduce; ring) (by ring)

omit [Fintype ι] in
lemma NCc.finsum {J : Type*} (s : Finset J) {N : J → LRule ι} {t : J → ℝ} :
    (∀ j ∈ s, NCc (N j) (t j)) → NCc (fun π x => ∑ j ∈ s, N j π x) (∑ j ∈ s, t j) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro _
    exact NCc.zero.congr (fun _ _ => by simp) (by simp)
  · intro a s ha ih h
    refine (NCc.add (h a (mem_insert_self a s))
      (ih fun j hj => h j (mem_insert_of_mem hj))).congr (fun _ _ => ?_) ?_
    · rw [sum_insert ha]
    · rw [sum_insert ha]

omit [Fintype ι] in
lemma NCc.total_nonneg {N : LRule ι} {t : ℝ} (h : NCc N t) : 0 ≤ t := by
  induction h with
  | zero => exact le_refl _
  | det _ _ _ hc => exact hc
  | add _ _ ih1 ih2 => linarith

omit [Fintype ι] in
lemma NCc.val_nonneg {N : LRule ι} {t : ℝ} (h : NCc N t) : ∀ π x, 0 ≤ N π x := by
  induction h with
  | zero => exact fun _ _ => le_refl _
  | det d c _ hc => exact fun π x => mul_nonneg hc (by unfold pt; split_ifs <;> norm_num)
  | add _ _ ih1 ih2 => exact fun π x => add_nonneg (ih1 π x) (ih2 π x)

omit [Fintype ι] in
lemma NCc.val_sum {N : LRule ι} {t : ℝ} (h : NCc N t) : ∀ π, N π 0 + N π 1 + N π 2 = t := by
  induction h with
  | zero => exact fun _ => by simp
  | det d c _ _ =>
    intro π
    beta_reduce
    generalize d π = y
    fin_cases y <;> norm_num [pt]
  | add _ _ ih1 ih2 => exact fun π => by beta_reduce; linarith [ih1 π, ih2 π]

omit [Fintype ι] in
lemma NCc.sdsp {N : LRule ι} {t : ℝ} (h : NCc N t) : SDSPn N := by
  induction h with
  | zero => exact fun π i => sdsp_const _ fun _ => rfl
  | det d c hd hc => exact fun π i => sdsp_smul hc (hd π i)
  | add _ _ ih1 ih2 => exact fun π i => sdsp_add (ih1 π i) (ih2 π i)

omit [Fintype ι] in
/-- Degrees of non-contextual rules are non-negative. -/
lemma NCc.deg_nonneg {N : LRule ι} {t : ℝ} (h : NCc N t) : ∀ π i, 0 ≤ degAt N π i := by
  induction h with
  | zero =>
    intro π i
    have : degAt (fun _ _ => (0 : ℝ)) π i = 0 := deg_zero
    rw [this]
  | det d c hd hc =>
    intro π i
    show 0 ≤ deg (fun r x => c * pt (d (Function.update π i r)) x)
    rw [deg_smul]
    exact mul_nonneg hc (det_deg_nonneg (fun r => d (Function.update π i r)) (hd π i))
  | @add N M s t _ _ ih1 ih2 =>
    intro π i
    show 0 ≤ deg (fun r x => N (Function.update π i r) x + M (Function.update π i r) x)
    rw [deg_add]
    exact add_nonneg (ih1 π i) (ih2 π i)

omit [Fintype ι] in
lemma NCc.eq_zero {N : LRule ι} (h : NCc N 0) : ∀ π x, N π x = 0 := by
  intro π x
  have hs : ∑ y, N π y = 0 := by rw [Fin.sum_univ_three]; exact h.val_sum π
  exact (sum_eq_zero_iff_of_nonneg fun y _ => h.val_nonneg π y).mp hs x (mem_univ x)

omit [Fintype ι] in
lemma detSP_const (a : Fin 3) : DetSP (ι := ι) fun _ => a :=
  fun _ _ => sdsp_const _ fun _ => rfl

omit [Fintype ι] in
lemma detSP_vtx (l : Fin 8) (i : ι) : DetSP (ι := ι) fun π => vtx l (π i) := by
  intro π k
  by_cases hk : k = i
  · subst hk
    have : slice (fun π x => pt (vtx l (π k)) x) π k = fun r => pt (vtx l r) := by
      funext r x
      simp [slice]
    rw [this]
    exact vtx_sdsp l
  · exact sdsp_const _ fun r => by simp [slice, Function.update_of_ne (Ne.symm hk)]

omit [Fintype ι] in
/-- Non-contextual rules are models. -/
lemma NC.model {N : LRule ι} (h : NC N) : Model N :=
  ⟨fun π => ⟨fun x => h.val_nonneg π x, h.val_sum π⟩, h.sdsp⟩

/-! ### Duples are non-contextual -/

/-- a is above b in ranking r (for a ≠ b). -/
def ab (a b : Fin 3) (r : Fin 6) : Prop := top r = a ∨ (sec r = a ∧ top r ≠ b)

instance (a b : Fin 3) (r : Fin 6) : Decidable (ab a b r) := by unfold ab; infer_instance

/-- The duple rule on {a, b} giving a the probability P. -/
noncomputable def dupR (a b : Fin 3) (P : Prof ι → ℝ) : LRule ι :=
  fun π x => P π * pt a x + (1 - P π) * pt b x

omit [Fintype ι] in
/-- Monotonicity in the comparison of a and b: a voter who prefers a cannot
    raise its probability by misreporting, one who prefers b cannot lower it. -/
def MonoAB (a b : Fin 3) (P : Prof ι → ℝ) : Prop :=
  ∀ π i r r', (ab a b r → P (Function.update π i r') ≤ P (Function.update π i r)) ∧
    (¬ ab a b r → P (Function.update π i r) ≤ P (Function.update π i r'))

omit [Fintype ι] in
lemma MonoAB.comp {a b : Fin 3} {P : Prof ι → ℝ} (h : MonoAB a b P) {φ : ℝ → ℝ}
    (hφ : Monotone φ) : MonoAB a b (fun π => φ (P π)) := fun π i r r' =>
  ⟨fun hr => hφ ((h π i r r').1 hr), fun hr => hφ ((h π i r r').2 hr)⟩

omit [Fintype ι] in
lemma sdsp_dupR {a b : Fin 3} {P : Prof ι → ℝ} (hP : MonoAB a b P) : SDSPn (dupR a b P) := by
  intro π i r r'
  obtain ⟨h1, h2⟩ := hP π i r r'
  simp only [slice, dupR]
  generalize P (Function.update π i r) = p at h1 h2 ⊢
  generalize P (Function.update π i r') = p' at h1 h2 ⊢
  refine ⟨?_, ?_⟩ <;> fin_cases a <;> fin_cases b <;> fin_cases r <;>
    simp [ab, pt, top, sec] at h1 h2 ⊢ <;> linarith

omit [Fintype ι] in
lemma mono_of_duple {K : LRule ι} (hK : Model K) {a b : Fin 3}
    (hz : ∀ π x, x ≠ a → x ≠ b → K π x = 0) : MonoAB a b (fun π => K π a) := by
  intro π i r r'
  obtain ⟨h1, h2⟩ := hK.2 π i r r'
  have s := (hK.1 (Function.update π i r)).2
  have s' := (hK.1 (Function.update π i r')).2
  have n0 := (hK.1 (Function.update π i r)).1
  have n0' := (hK.1 (Function.update π i r')).1
  have z0 := hz (Function.update π i r) 0
  have z1 := hz (Function.update π i r) 1
  have z2 := hz (Function.update π i r) 2
  have z0' := hz (Function.update π i r') 0
  have z1' := hz (Function.update π i r') 1
  have z2' := hz (Function.update π i r') 2
  have m0 := n0 0; have m1 := n0 1; have m2 := n0 2
  have m0' := n0' 0; have m1' := n0' 1; have m2' := n0' 2
  simp only [slice] at h1 h2
  show (ab a b r → K (Function.update π i r') a ≤ K (Function.update π i r) a) ∧
    (¬ ab a b r → K (Function.update π i r) a ≤ K (Function.update π i r') a)
  clear n0 n0'
  generalize K (Function.update π i r) = q at *
  generalize K (Function.update π i r') = q' at *
  fin_cases a <;> fin_cases b <;> fin_cases r <;>
    simp [ab, top, sec] at h1 h2 z0 z1 z2 z0' z1' z2' ⊢ <;> linarith

/-- A monotone duple is non-contextual: it is a mixture of monotone
    yes-or-no duples. By induction on the number of profiles with a value
    strictly between 0 and 1: split off the least such value v, as
    P = v · [P > 0] + (1 − v) · max(0, (P − v)/(1 − v)). -/
lemma nc_dupR (a b : Fin 3) :
    ∀ N (P : Prof ι → ℝ), (∀ π, 0 ≤ P π ∧ P π ≤ 1) → MonoAB a b P →
      (univ.filter fun π => 0 < P π ∧ P π < 1).card = N → NC (dupR a b P) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro P hb hm hN
    by_cases hS : (univ.filter fun π => 0 < P π ∧ P π < 1).Nonempty
    · -- split off the least value strictly between 0 and 1
      set S := univ.filter fun π => 0 < P π ∧ P π < 1
      have hI : (S.image P).Nonempty := hS.image P
      set v := (S.image P).min' hI with hv
      obtain ⟨πv, hπvS, hπv⟩ := mem_image.mp ((S.image P).min'_mem hI)
      have hπvS' := (mem_filter.mp hπvS).2
      have hv0 : 0 < v := by rw [hv, ← hπv]; exact hπvS'.1
      have hv1 : v < 1 := by rw [hv, ← hπv]; exact hπvS'.2
      have hvle : ∀ π, P π = 0 ∨ v ≤ P π := by
        intro π
        rcases (hb π).1.eq_or_lt with h | h
        · exact Or.inl h.symm
        · right
          rcases (hb π).2.lt_or_eq with h' | h'
          · exact (S.image P).min'_le _ (mem_image.mpr ⟨π, mem_filter.mpr ⟨mem_univ _, h, h'⟩, rfl⟩)
          · rw [h']; exact hv1.le
      let B : Prof ι → ℝ := fun π => if 0 < P π then 1 else 0
      let P' : Prof ι → ℝ := fun π => max 0 ((P π - v) / (1 - v))
      have hBm : MonoAB a b B := hm.comp (φ := fun t => if 0 < t then 1 else 0) (by
        intro s t hst
        dsimp only
        split_ifs with h1 h2 <;> first | exact absurd (lt_of_lt_of_le h1 hst) h2 | norm_num)
      have hP'm : MonoAB a b P' := hm.comp (φ := fun t => max 0 ((t - v) / (1 - v))) (by
        intro s t hst
        exact max_le_max (le_refl _) (div_le_div_of_nonneg_right (by linarith) (by linarith)))
      have hBb : ∀ π, 0 ≤ B π ∧ B π ≤ 1 := fun π => by
        simp only [B]; split_ifs <;> norm_num
      have hP'b : ∀ π, 0 ≤ P' π ∧ P' π ≤ 1 := fun π => by
        refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
        rw [div_le_one (by linarith)]
        linarith [(hb π).2]
      have hBc : (univ.filter fun π => 0 < B π ∧ B π < 1).card = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]
        intro π _ h
        simp only [B] at h
        split_ifs at h <;> norm_num at h
      have hP'c : (univ.filter fun π => 0 < P' π ∧ P' π < 1).card < N := by
        rw [← hN]
        apply card_lt_card
        rw [ssubset_iff_of_subset]
        · refine ⟨πv, hπvS, ?_⟩
          simp only [mem_filter, mem_univ, true_and, not_and, P']
          intro h
          rw [hπv, ← hv, sub_self, zero_div, max_self] at h
          exact absurd h (lt_irrefl 0)
        · intro π hπ
          simp only [mem_filter, mem_univ, true_and, P'] at hπ ⊢
          obtain ⟨h1, h2⟩ := hπ
          have hpos : 0 < (P π - v) / (1 - v) := by
            by_contra hc
            push Not at hc
            rw [max_eq_left hc] at h1
            exact lt_irrefl 0 h1
          rw [max_eq_right hpos.le, div_lt_one (by linarith)] at h2
          rw [lt_div_iff₀ (by linarith)] at hpos
          exact mem_filter.mpr ⟨mem_univ _, by linarith, by linarith⟩
      have hNpos : 0 < N := by rw [← hN]; exact card_pos.mpr hS
      have hB := ih 0 hNpos B hBb hBm hBc
      have hP' := ih _ hP'c P' hP'b hP'm rfl
      refine (NCc.add (hB.smul hv0.le) (hP'.smul (by linarith : (0 : ℝ) ≤ 1 - v))).congr
        (fun π x => ?_) (by ring)
      simp only [dupR, B, P']
      rcases hvle π with h | h
      · rw [h, ite_eq_right (lt_irrefl 0),
          max_eq_left (div_nonpos_iff.mpr (Or.inr ⟨by linarith, by linarith⟩))]
        ring
      · have hne : (1 : ℝ) - v ≠ 0 := by linarith
        rw [ite_eq_left (by linarith : (0 : ℝ) < P π),
          max_eq_right (div_nonneg (by linarith) (by linarith))]
        field_simp
        ring
    · -- P takes only the values 0 and 1: a deterministic SP duple
      rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at hS
      have h01 : ∀ π, P π = 0 ∨ P π = 1 := by
        intro π
        have := hS (mem_univ π)
        rcases (hb π).1.eq_or_lt with h | h
        · exact Or.inl h.symm
        · rcases (hb π).2.lt_or_eq with h' | h'
          · exact absurd ⟨h, h'⟩ this
          · exact Or.inr h'
      let d : Prof ι → Fin 3 := fun π => if P π = 1 then a else b
      have hd : ∀ π x, 1 * pt (d π) x = dupR a b P π x := by
        intro π x
        simp only [dupR, d]
        rcases h01 π with h | h
        · rw [h, ite_eq_right (by norm_num : ¬ (0 : ℝ) = 1)]
          ring
        · rw [h, ite_eq_left rfl]
          ring
      have hdet : DetSP d := by
        have : (fun π x => pt (d π) x) = dupR a b P := by
          funext π x
          rw [← hd]
          ring
        unfold DetSP
        rw [this]
        exact sdsp_dupR hm
      exact (NCc.det d 1 hdet zero_le_one).congr hd rfl

omit [Fintype ι] in
lemma NCc_det_one {d : Prof ι → Fin 3} (hd : DetSP d) : NC (fun π x => pt (d π) x) :=
  (NCc.det d 1 hd zero_le_one).congr (fun _ _ => one_mul _) rfl

/-- Duple components are non-contextual. -/
lemma nc_duple {K : LRule ι} (hK : Model K) (hD : Duple K) : NC K := by
  obtain ⟨a, b, hz⟩ := hD
  by_cases hab : a = b
  · subst hab
    refine (NCc_det_one (detSP_const (ι := ι) a)).congr (fun π x => ?_) rfl
    have s := (hK.1 π).2
    have h0 := hz π 0; have h1 := hz π 1; have h2 := hz π 2
    fin_cases a <;> fin_cases x <;> simp [pt] at h0 h1 h2 ⊢ <;> linarith
  · have hb : ∀ π, 0 ≤ K π a ∧ K π a ≤ 1 := by
      intro π
      have s := (hK.1 π).2
      have n := (hK.1 π).1
      refine ⟨n a, ?_⟩
      calc K π a ≤ ∑ y, K π y := single_le_sum (fun y _ => n y) (mem_univ a)
        _ = 1 := by rw [Fin.sum_univ_three]; exact s
    refine (nc_dupR a b _ (fun π => K π a) hb (mono_of_duple hK hz) rfl).congr
      (fun π x => ?_) rfl
    have s := (hK.1 π).2
    have h0 := hz π 0; have h1 := hz π 1; have h2 := hz π 2
    simp only [dupR]
    fin_cases a <;> fin_cases b <;> fin_cases x <;> simp [pt] at hab h0 h1 h2 ⊢ <;> linarith

/-! ### Degrees of the components -/

omit [Fintype ι] in
lemma degAt_uni_ne {K : LRule ι} {k : ι} (hK : ∀ π π' : Prof ι, π k = π' k → K π = K π')
    {i : ι} (hik : i ≠ k) (π : Prof ι) : degAt K π i = 0 :=
  deg_const _ (slice_const_of_ne hK hik π)

omit [Fintype ι] in
lemma degAt_duple {K : LRule ι} (hK : Model K) (hD : Duple K) (π : Prof ι) (i : ι) :
    degAt K π i = 0 := by
  obtain ⟨a, b, hz⟩ := hD
  obtain ⟨z, hza, hzb⟩ := exists_third a b
  exact duple_deg (lottery_slice hK.1 π i) (hK.2 π i) z fun r => hz _ z hza hzb

/-- For a unilateral or duple model, the negative parts of the degrees sum to
    at most 1/2: only the deciding voter can have a negative degree, and it is
    at least −1/2 by Proposition 4. -/
lemma component_bound {K : LRule ι} (hK : Model K) (hUD : Unilateral K ∨ Duple K)
    (π : Prof ι) : ∑ i, max 0 (-degAt K π i) ≤ 1 / 2 := by
  rcases hUD with ⟨k, hk⟩ | hD
  · rw [sum_eq_single k (fun i _ hik => by rw [degAt_uni_ne hk hik π, neg_zero, max_self])
      (fun h => absurd (mem_univ k) h)]
    have h := deg_ge (lottery_slice hK.1 π k) (hK.2 π k)
    exact max_le (by norm_num) (by show -deg (slice K π k) ≤ 1 / 2; linarith)
  · rw [sum_eq_zero fun i _ => by rw [degAt_duple hK hD π i, neg_zero, max_self]]
    norm_num

/-- **The bound on models.** Under Gibbard's theorem, the negative parts of
    the degrees of any model sum to at most 1/2. -/
lemma model_bound (hG : Gibbard1977 ι) {M : LRule ι} (hM : Model M) (π : Prof ι) :
    ∑ i, max 0 (-degAt M π i) ≤ 1 / 2 := by
  obtain ⟨n, w, K, hw0, hw1, hKm, hUD, hMK⟩ := hG M hM
  have hMeq : M = fun π x => ∑ j, w j * K j π x := funext fun π => funext (hMK π)
  have hd : ∀ i, degAt M π i = ∑ j, w j * degAt (K j) π i := fun i => by
    rw [hMeq, degAt_sum]
  calc ∑ i, max 0 (-degAt M π i)
      ≤ ∑ i, ∑ j, w j * max 0 (-degAt (K j) π i) := by
        refine sum_le_sum fun i _ => max_le (sum_nonneg fun j _ =>
          mul_nonneg (hw0 j) (le_max_left _ _)) ?_
        rw [hd i, ← sum_neg_distrib]
        exact sum_le_sum fun j _ => by
          rw [neg_mul_eq_mul_neg]
          exact mul_le_mul_of_nonneg_left (le_max_right _ _) (hw0 j)
    _ = ∑ j, w j * ∑ i, max 0 (-degAt (K j) π i) := by
        rw [sum_comm]
        exact sum_congr rfl fun j _ => (mul_sum _ _ _).symm
    _ ≤ ∑ j, w j * (1 / 2) :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (component_bound (hKm j) (hUD j) π) (hw0 j)
    _ = 1 / 2 := by rw [← sum_mul, hw1, one_mul]

/-! ### The lower bound on the contextual fraction -/

/-- **The lower bound.** In any decomposition L = (1 − λ) N + λ M with N
    non-contextual and M a model, λ ≥ 2 · Σ_i max(0, −deg_i). -/
theorem cf_lower (hG : Gibbard1977 ι) {L N M : LRule ι} {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hN : NC N) (hM : Model M) (hL : ∀ π x, L π x = (1 - lam) * N π x + lam * M π x)
    (π : Prof ι) : 2 * ∑ i, max 0 (-degAt L π i) ≤ lam := by
  have hd : ∀ i, degAt L π i = (1 - lam) * degAt N π i + lam * degAt M π i := fun i => by
    unfold degAt slice
    rw [← deg_smul, ← deg_smul, ← deg_add]
    congr 1
    funext r x
    exact hL _ x
  have hterm : ∀ i, max 0 (-degAt L π i) ≤ lam * max 0 (-degAt M π i) := fun i => by
    refine max_le (mul_nonneg h0 (le_max_left _ _)) ?_
    rw [hd i]
    have := hN.deg_nonneg π i
    have := mul_le_mul_of_nonneg_left (le_max_right 0 (-degAt M π i)) h0
    nlinarith
  have hb := model_bound hG hM π
  calc 2 * ∑ i, max 0 (-degAt L π i) ≤ 2 * ∑ i, lam * max 0 (-degAt M π i) := by
        have := sum_le_sum fun i (_ : i ∈ univ) => hterm i
        linarith
    _ = 2 * lam * ∑ i, max 0 (-degAt M π i) := by rw [← mul_sum]; ring
    _ ≤ 2 * lam * (1 / 2) := mul_le_mul_of_nonneg_left hb (by linarith)
    _ = lam := by ring

/-! ### The decomposition -/

/-- **Proposition 5, the decomposition.** Under Gibbard's theorem, every
    SD-SP lottery rule is a non-contextual part plus random top twos, voter i's
    with weight 2 · max(0, −deg_i); and the degrees do not depend on the
    context. -/
theorem prop5_decomp (hG : Gibbard1977 ι) [Nonempty ι] {L : LRule ι} (hL : Model L) :
    ∃ (N : LRule ι) (c D : ι → ℝ), NCc N (1 - ∑ i, c i) ∧ (∀ i, 0 ≤ c i) ∧
      (∀ π i, degAt L π i = D i) ∧ (∀ i, c i = 2 * max 0 (-D i)) ∧
      ∀ π x, L π x = N π x + ∑ i, c i * T2 i π x := by
  classical
  obtain ⟨n, w, K, hw0, hw1, hKm, hUD, hLK⟩ := hG L hL
  -- the deciding voter of each unilateral component
  let isU : Fin n → Prop := fun j => Unilateral (K j)
  let k : Fin n → ι := fun j => if h : isU j then Classical.choose h else Classical.arbitrary ι
  have hk : ∀ j, isU j → ∀ π π' : Prof ι, π (k j) = π' (k j) → K j π = K j π' := by
    intro j h
    have := Classical.choose_spec h
    simpa [k, h] using this
  let g : Fin n → Rule := fun j r => K j (fun _ => r)
  have hKg : ∀ j, isU j → ∀ π, K j π = g j (π (k j)) := fun j h π => hk j h π _ rfl
  have hslice : ∀ j, isU j → ∀ π, slice (K j) π (k j) = g j := fun j h π => by
    funext r
    simp only [slice]
    rw [hKg j h, Function.update_self]
  have hgL : ∀ j, isU j → Lottery (g j) := fun j _ r => (hKm j).1 (fun _ => r)
  have hgS : ∀ j, isU j → SDSP (g j) := fun j h => by
    rw [← hslice j h (fun _ => 0)]
    exact (hKm j).2 _ _
  -- grouping by voter
  let U : ι → Finset (Fin n) := fun i => (univ.filter isU).filter fun j => k j = i
  let Dp : Finset (Fin n) := univ.filter fun j => ¬ isU j
  let u : ι → ℝ := fun i => ∑ j ∈ U i, w j
  let G : ι → Rule := fun i r x => ∑ j ∈ U i, w j * g j r x
  have hUmem : ∀ i j, j ∈ U i ↔ isU j ∧ k j = i := fun i j => by
    simp [U]
  have hu0 : ∀ i, 0 ≤ u i := fun i => sum_nonneg fun j _ => hw0 j
  -- the degree of L
  have hdegG : ∀ π i, degAt L π i = deg (G i) := by
    intro π i
    have hLeq : L = fun π x => ∑ j, w j * K j π x := funext fun π => funext (hLK π)
    rw [hLeq, degAt_sum]
    have : ∀ j, w j * degAt (K j) π i = if j ∈ U i then w j * deg (g j) else 0 := by
      intro j
      by_cases hj : j ∈ U i
      · rw [ite_eq_left hj]
        obtain ⟨hju, hjk⟩ := (hUmem i j).mp hj
        unfold degAt
        rw [← hjk, hslice j hju]
      · rw [ite_eq_right hj]
        by_cases hju : isU j
        · have hki : i ≠ k j := fun e => hj ((hUmem i j).mpr ⟨hju, e.symm⟩)
          rw [degAt_uni_ne (hk j hju) hki π, mul_zero]
        · rcases hUD j with h | h
          · exact absurd h hju
          · rw [degAt_duple (hKm j) h π i, mul_zero]
    rw [sum_congr rfl fun j _ => this j, sum_ite_mem, univ_inter]
    show _ = deg (fun r x => ∑ j ∈ U i, w j * g j r x)
    rw [deg_sum]
    exact sum_congr rfl fun j _ => (deg_smul _ _).symm
  -- each group, normalised, is a one-voter SD-SP lottery
  have hGL : ∀ i, 0 < u i → Lottery (fun r x => G i r x / u i) := by
    intro i hu r
    refine ⟨fun x => div_nonneg (sum_nonneg fun j hj =>
      mul_nonneg (hw0 j) ((hgL j ((hUmem i j).mp hj).1 r).1 x)) hu.le, ?_⟩
    show G i r 0 / u i + G i r 1 / u i + G i r 2 / u i = 1
    rw [← add_div, ← add_div, div_eq_one_iff_eq hu.ne']
    simp only [G, ← sum_add_distrib, ← mul_add]
    exact sum_congr rfl fun j hj => by rw [(hgL j ((hUmem i j).mp hj).1 r).2, mul_one]
  have hGS : ∀ i, 0 < u i → SDSP (fun r x => G i r x / u i) := by
    intro i hu r r'
    have h := fun j (hj : j ∈ U i) => hgS j ((hUmem i j).mp hj).1 r r'
    beta_reduce
    refine ⟨div_le_div_of_nonneg_right (sum_le_sum fun j hj =>
      mul_le_mul_of_nonneg_left (h j hj).1 (hw0 j)) hu.le, ?_⟩
    rw [← add_div, ← add_div]
    refine div_le_div_of_nonneg_right ?_ hu.le
    simp only [G, ← sum_add_distrib, ← mul_add]
    exact sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (h j hj).2 (hw0 j)
  -- Proposition 4 for each group
  have hω : ∀ i, ∃ ω : Fin 8 → ℝ, (∀ l, 0 ≤ ω l) ∧ ∑ l, ω l = 1 ∧
      (∀ r x, G i r x = u i * mix ω r x) ∧ u i * ω 7 = max 0 (-2 * deg (G i)) := by
    intro i
    by_cases hu : 0 < u i
    · obtain ⟨ω, hω0, hω1, hωf, hω7⟩ := decomp (hGL i hu) (hGS i hu)
      refine ⟨ω, hω0, hω1, fun r x => ?_, ?_⟩
      · have hu' := hu.ne'
        have := congrFun (congrFun hωf r) x
        rw [← this]
        field_simp
      · have hu' := hu.ne'
        rw [hω7, mul_max_of_nonneg _ _ hu.le, mul_zero]
        congr 1
        have : (fun r x => G i r x / u i) = fun r x => (u i)⁻¹ * G i r x := by
          funext r x; ring
        rw [this, deg_smul]
        field_simp
    · have hu' : u i = 0 := le_antisymm (not_lt.mp hu) (hu0 i)
      have hwz : ∀ j ∈ U i, w j = 0 := (sum_eq_zero_iff_of_nonneg fun j _ => hw0 j).mp hu'
      have hG0 : ∀ r x, G i r x = 0 := fun r x =>
        sum_eq_zero fun j hj => by rw [hwz j hj, zero_mul]
      refine ⟨Pi.single 0 1, fun l => ?_, ?_, fun r x => by rw [hG0, hu', zero_mul], ?_⟩
      · by_cases hl : l = 0
        · subst hl; simp
        · simp [hl]
      · simp
      · have : deg (G i) = 0 := by
          unfold deg
          simp only [hG0]
          ring
        rw [this, hu']
        simp
  choose ω hω0 hω1 hωG hω7 using hω
  -- the pieces
  let c : ι → ℝ := fun i => u i * ω i 7
  let Nd : LRule ι := fun π x =>
    ∑ i, ∑ l ∈ univ.erase 7, (u i * ω i l) * pt (vtx l (π i)) x + ∑ j ∈ Dp, w j * K j π x
  have hsplit : ∑ j, w j = ∑ i, u i + ∑ j ∈ Dp, w j := by
    rw [← sum_filter_add_sum_filter_not univ isU]
    congr 1
    exact (sum_fiberwise (univ.filter isU) k w).symm
  have hNd : NCc Nd (1 - ∑ i, c i) := by
    refine (NCc.add (NCc.finsum univ fun i _ => NCc.finsum (univ.erase 7) fun l _ =>
      NCc.det (fun π => vtx l (π i)) (u i * ω i l) (detSP_vtx l i)
        (mul_nonneg (hu0 i) (hω0 i l)))
      (NCc.finsum Dp fun j hj => (nc_duple (hKm j) ((hUD j).resolve_left
        (mem_filter.mp hj).2)).smul (hw0 j))).congr (fun _ _ => rfl) ?_
    have h7 : ∀ i, ∑ l ∈ univ.erase 7, u i * ω i l = u i - u i * ω i 7 := fun i => by
      rw [← mul_sum, sum_erase_eq_sub (mem_univ _), hω1 i]
      ring
    simp only [h7, mul_one, sum_sub_distrib]
    rw [hw1] at hsplit
    simp only [c]
    linarith
  refine ⟨Nd, c, fun i => deg (G i), hNd, fun i => mul_nonneg (hu0 i) (hω0 i 7),
    hdegG, fun i => by show u i * ω i 7 = _; rw [hω7 i, max_two], fun π x => ?_⟩
  -- the equation
  have hunil : ∑ j ∈ univ.filter isU, w j * K j π x = ∑ i, G i (π i) x := by
    rw [← sum_fiberwise (univ.filter isU) k]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j hj => ?_
    obtain ⟨hju, hjk⟩ := (hUmem i j).mp hj
    rw [hKg j hju, hjk]
  rw [hLK, ← sum_filter_add_sum_filter_not univ isU, hunil]
  simp only [hωG, mix_split, Nd, Dp, c, mul_add, sum_add_distrib, mul_sum, T2]
  simp only [← mul_assoc]
  ring

/-! ### Proposition 5 -/

omit [Fintype ι] in
lemma sdsp_finsum {J : Type*} (s : Finset J) (c : J → ℝ) (f : J → Rule) :
    (∀ j ∈ s, 0 ≤ c j) → (∀ j ∈ s, SDSP (f j)) →
      SDSP (fun r x => ∑ j ∈ s, c j * f j r x) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro _ _
    exact sdsp_const _ fun _ => by simp
  · intro a s ha ih hc hf
    simp only [sum_insert ha]
    exact sdsp_add (sdsp_smul (hc a (mem_insert_self _ _)) (hf a (mem_insert_self _ _)))
      (ih (fun j hj => hc j (mem_insert_of_mem hj)) (fun j hj => hf j (mem_insert_of_mem hj)))

/-- The converse: a non-contextual part plus random top twos, of total
    weight 1, is a model. -/
theorem model_of_decomp {N : LRule ι} {c : ι → ℝ} (hN : NCc N (1 - ∑ i, c i))
    (hc : ∀ i, 0 ≤ c i) : Model (fun π x => N π x + ∑ i, c i * T2 i π x) := by
  refine ⟨fun π => ⟨fun x => add_nonneg (hN.val_nonneg π x) (sum_nonneg fun i _ =>
    mul_nonneg (hc i) (((t2_model i).1 π).1 x)), ?_⟩, fun π k => ?_⟩
  · have h := hN.val_sum π
    have ht : ∀ i, T2 i π 0 + T2 i π 1 + T2 i π 2 = 1 := fun i => ((t2_model i).1 π).2
    have : ∑ i, c i * T2 i π 0 + ∑ i, c i * T2 i π 1 + ∑ i, c i * T2 i π 2 = ∑ i, c i := by
      rw [← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun i _ => by rw [← mul_add, ← mul_add, ht i, mul_one]
    beta_reduce
    linarith
  · exact sdsp_add (hN.sdsp π k) (sdsp_finsum univ c (fun i => slice (T2 i) π k)
      (fun i _ => hc i) (fun i _ => (t2_model i).2 π k))

/-- **Context independence.** Under Gibbard's theorem the degree of a voter
    in an SD-SP lottery rule does not depend on the context. -/
theorem deg_indep (hG : Gibbard1977 ι) [Nonempty ι] {L : LRule ι} (hL : Model L)
    (π π' : Prof ι) (i : ι) : degAt L π i = degAt L π' i := by
  obtain ⟨-, -, D, -, -, hD, -⟩ := prop5_decomp hG hL
  rw [hD π i, hD π' i]

/-- **Proposition 5, non-contextuality.** An SD-SP lottery rule is a mixture
    of deterministic SP rules exactly when no degree is negative. -/
theorem nc_iff (hG : Gibbard1977 ι) [Nonempty ι] {L : LRule ι} (hL : Model L) :
    NC L ↔ ∀ π i, 0 ≤ degAt L π i := by
  constructor
  · exact fun h => h.deg_nonneg
  · intro hd
    obtain ⟨N, c, D, hN, -, hDL, hc, hLN⟩ := prop5_decomp hG hL
    have hc0 : ∀ i, c i = 0 := fun i => by
      have hD0 : 0 ≤ D i := hDL (fun _ => 0) i ▸ hd (fun _ => 0) i
      have : max 0 (-D i) = 0 := max_eq_left (by linarith)
      rw [hc i, this, mul_zero]
    simp only [hc0, zero_mul, sum_const_zero, sub_zero] at hN hLN
    exact hN.congr (fun π x => by rw [hLN π x, add_zero]) rfl

/-- **Proposition 5, the contextual fraction.** The least weight of a model in
    a decomposition of L into a non-contextual rule and a model is
    2 · Σ_i max(0, −deg_i). -/
theorem cf (hG : Gibbard1977 ι) [Nonempty ι] {L : LRule ι} (hL : Model L) (π : Prof ι) :
    IsLeast {lam : ℝ | 0 ≤ lam ∧ lam ≤ 1 ∧ ∃ N M : LRule ι, NC N ∧ Model M ∧
      ∀ π x, L π x = (1 - lam) * N π x + lam * M π x}
      (2 * ∑ i, max 0 (-degAt L π i)) := by
  refine ⟨?_, fun lam ⟨h0, h1, N, M, hN, hM, hLNM⟩ => cf_lower hG h0 h1 hN hM hLNM π⟩
  obtain ⟨N, c, D, hN, hc0, hDL, hc, hLN⟩ := prop5_decomp hG hL
  have hlam : ∑ i, c i = 2 * ∑ i, max 0 (-degAt L π i) := by
    rw [mul_sum]
    exact sum_congr rfl fun i _ => by rw [hc i, hDL π i]
  rw [← hlam]
  set lam := ∑ i, c i with hlamdef
  have hl0 : 0 ≤ lam := sum_nonneg fun i _ => hc0 i
  have hl1 : lam ≤ 1 := by linarith [hN.total_nonneg]
  refine ⟨hl0, hl1, ?_⟩
  -- the non-contextual part, normalised
  obtain ⟨N1, hN1, hNN1⟩ : ∃ N1 : LRule ι, NC N1 ∧ ∀ π x, N π x = (1 - lam) * N1 π x := by
    rcases hl1.lt_or_eq with h | h
    · have hne : (1 : ℝ) - lam ≠ 0 := by linarith
      refine ⟨fun π x => (1 - lam)⁻¹ * N π x, (hN.smul (inv_nonneg.mpr (by linarith))).congr
        (fun _ _ => rfl) (by field_simp), fun π x => by field_simp⟩
    · refine ⟨fun π x => pt 0 x, NCc_det_one (detSP_const 0), fun π x => ?_⟩
      have h0' : NCc N 0 := hN.congr (fun _ _ => rfl) (by rw [h]; ring)
      rw [h0'.eq_zero π x, h]
      ring
  -- the random top twos, normalised
  obtain ⟨M1, hM1, hMM1⟩ : ∃ M1 : LRule ι, Model M1 ∧
      ∀ π x, ∑ i, c i * T2 i π x = lam * M1 π x := by
    rcases hl0.lt_or_eq with h | h
    · have hm := model_of_decomp (N := fun _ _ => 0)
        (c := fun i => c i / lam) (NCc.zero.congr (fun _ _ => rfl) (by
          rw [← sum_div, ← hlamdef, div_self h.ne']; ring))
        (fun i => div_nonneg (hc0 i) hl0)
      refine ⟨_, hm, fun π x => ?_⟩
      have hne := h.ne'
      simp only [zero_add, mul_sum]
      exact sum_congr rfl fun i _ => by field_simp
    · have hcz : ∀ i, c i = 0 := fun i =>
        (sum_eq_zero_iff_of_nonneg fun i _ => hc0 i).mp h.symm i (mem_univ i)
      refine ⟨fun π x => pt 0 x, (NCc_det_one (detSP_const 0)).model, fun π x => ?_⟩
      simp [hcz, ← h]
  exact ⟨N1, M1, hN1, hM1, fun π x => by rw [hLN, hNN1, hMM1]⟩

end ContextualFraction

/-
  Lemma 3 of *Four Levels* (the joint draw), both directions
  (*Consistency as an Extension Problem*, Section 3b).

  For lotteries μ, ν, λ over the candidates, winners X ~ μ, Y ~ ν, Z ~ λ can
  be drawn jointly so that X = Y implies Z = X exactly when
  λ(a) ≥ μ(a) + ν(a) − 1 for every candidate a (`lemma3`). The necessary
  direction is `JoinLotteries.lemma3_nec`; this file adds the sufficient one
  (`lemma3_suff`), following the hand proof:

  * At most one candidate has μ(a) + ν(a) > 1. Put d(a) = max(0, μ(a) + ν(a) − 1)
    on X = Y = Z = a.
  * The remaining masses μ − d and ν − d have equal total 1 − Σ d, and no
    candidate carries more than that of both together. Such masses admit a
    coupling with nothing on the diagonal (`offDiag_of_fits`): if a candidate
    carries exactly the total, it exchanges its mass with all others
    (`offDiag_tight`); otherwise some mass moves to an off-diagonal cell until
    a mass vanishes or a candidate becomes tight (induction on the number of
    candidates carrying mass).
  * Off the diagonal, Z is drawn independently from λ − d, rescaled.

  The coupling lemma is the transport fact behind the joint draw, of Hall
  type, and is stated separately for reuse.

  Strassen's theorem for a chain (`mono_iff_dom`): on the positions of a
  ranking, a coupling that moves probability only upwards exists exactly when
  one lottery stochastically dominates the other. The coupling is the quantile
  coupling, by overlaps of intervals (`ov`). This is condition (E) of the
  reduction proposition of *Consistency as an Extension Problem*, Section 3c.
-/

module

public import JoinLotteries

@[expose] public section

open Finset

namespace Couplings

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Couplings without mass on the diagonal -/

/-- A coupling of m₁ and m₂ that puts no mass on the diagonal. -/
def OffDiag (m₁ m₂ : α → ℝ) : Prop :=
  ∃ P : α → α → ℝ, (∀ x y, 0 ≤ P x y) ∧ (∀ x, ∑ y, P x y = m₁ x) ∧
    (∀ y, ∑ x, P x y = m₂ y) ∧ ∀ x, P x x = 0

/-- Nonnegative masses of total T each, no candidate carrying more than T of
    both together. -/
structure Fits (m₁ m₂ : α → ℝ) (T : ℝ) : Prop where
  nonneg₁ : ∀ b, 0 ≤ m₁ b
  nonneg₂ : ∀ b, 0 ≤ m₂ b
  sum₁ : ∑ b, m₁ b = T
  sum₂ : ∑ b, m₂ b = T
  le : ∀ b, m₁ b + m₂ b ≤ T

lemma sum_off (f : α → ℝ) (a : α) : ∑ y, (if y = a then 0 else f y) = ∑ y, f y - f a := by
  have h1 : ∑ y, (if y = a then f y else 0) = f a := by simp
  have h2 : ∑ y, ((if y = a then 0 else f y) + (if y = a then f y else 0)) = ∑ y, f y :=
    sum_congr rfl fun y _ => by split_ifs <;> simp
  rw [sum_add_distrib, h1] at h2
  linarith

/-- The coupling when candidate a carries exactly the total: a's row takes the
    others' second masses, a's column the others' first masses. -/
def tightP (m₁ m₂ : α → ℝ) (a x y : α) : ℝ :=
  if x = a then (if y = a then 0 else m₂ y) else (if y = a then m₁ x else 0)

lemma offDiag_tight {m₁ m₂ : α → ℝ} {T : ℝ} (h : Fits m₁ m₂ T) (a : α)
    (ha : m₁ a + m₂ a = T) : OffDiag m₁ m₂ := by
  refine ⟨tightP m₁ m₂ a, ?_, ?_, ?_, ?_⟩
  · intro x y
    unfold tightP
    split_ifs <;> first | exact le_refl 0 | exact h.nonneg₂ y | exact h.nonneg₁ x
  · intro x
    by_cases hx : x = a
    · rw [hx]
      unfold tightP
      simp only [↓reduceIte]
      rw [sum_off, h.sum₂]
      linarith
    · simp [tightP, hx]
  · intro y
    by_cases hy : y = a
    · rw [hy]
      unfold tightP
      simp only [↓reduceIte]
      rw [sum_off, h.sum₁]
      linarith
    · simp [tightP, hy]
  · intro x
    by_cases hx : x = a <;> simp [tightP, hx]

/-- Adding mass t ≥ 0 on the off-diagonal cell (x, y). -/
lemma offDiag_add {m₁ m₂ : α → ℝ} {x y : α} (hxy : x ≠ y) (t : ℝ) (ht : 0 ≤ t)
    (h : OffDiag (fun b => m₁ b - if b = x then t else 0) (fun b => m₂ b - if b = y then t else 0)) :
    OffDiag m₁ m₂ := by
  obtain ⟨P, h0, hr, hc, hd⟩ := h
  refine ⟨fun x' y' => P x' y' + if x' = x ∧ y' = y then t else 0, ?_, ?_, ?_, ?_⟩
  · intro x' y'
    show 0 ≤ P x' y' + (if x' = x ∧ y' = y then t else 0)
    have := h0 x' y'
    split_ifs <;> linarith
  · intro x'
    show ∑ y', (P x' y' + if x' = x ∧ y' = y then t else 0) = m₁ x'
    rw [sum_add_distrib, hr x']
    by_cases hx : x' = x
    · simp [hx]
    · simp [hx]
  · intro y'
    show ∑ x', (P x' y' + if x' = x ∧ y' = y then t else 0) = m₂ y'
    rw [sum_add_distrib, hc y']
    by_cases hy : y' = y
    · simp [hy]
    · simp [hy]
  · intro x'
    show P x' x' + (if x' = x ∧ x' = y then t else 0) = 0
    rw [hd x']
    have : ¬ (x' = x ∧ x' = y) := fun h => hxy (h.1.symm.trans h.2)
    simp [this]

/-- Removing t from m₁ at x and from m₂ at y keeps the hypotheses, with total
    T − t, when t fits and no third candidate exceeds T − t. -/
lemma fits_sub {m₁ m₂ : α → ℝ} {T : ℝ} (h : Fits m₁ m₂ T) {x y : α} (hxy : x ≠ y) {t : ℝ}
    (ht1 : t ≤ m₁ x) (ht2 : t ≤ m₂ y)
    (hrest : ∀ b, b ≠ x → b ≠ y → m₁ b + m₂ b ≤ T - t) :
    Fits (fun b => m₁ b - if b = x then t else 0) (fun b => m₂ b - if b = y then t else 0)
      (T - t) where
  nonneg₁ b := by
    by_cases hb : b = x
    · simp only [hb, ↓reduceIte]
      linarith
    · simp only [hb, ↓reduceIte]
      linarith [h.nonneg₁ b]
  nonneg₂ b := by
    by_cases hb : b = y
    · simp only [hb, ↓reduceIte]
      linarith
    · simp only [hb, ↓reduceIte]
      linarith [h.nonneg₂ b]
  sum₁ := by
    rw [sum_sub_distrib, h.sum₁]
    simp
  sum₂ := by
    rw [sum_sub_distrib, h.sum₂]
    simp
  le b := by
    by_cases hbx : b = x
    · simp only [hbx, hxy, ↓reduceIte]
      linarith [h.le x]
    · by_cases hby : b = y
      · simp only [hby, hxy.symm, ↓reduceIte]
        linarith [h.le y]
      · simp only [hbx, hby, ↓reduceIte]
        linarith [hrest b hbx hby]

/-- The number of candidates carrying mass, counted for both masses. -/
noncomputable def suppCard (m₁ m₂ : α → ℝ) : ℕ :=
  (univ.filter (fun b => m₁ b ≠ 0)).card + (univ.filter (fun b => m₂ b ≠ 0)).card

lemma suppCard_lt {m₁ m₂ : α → ℝ} {x y : α} (hx : 0 < m₁ x) (hy : 0 < m₂ y) :
    suppCard (fun b => m₁ b - if b = x then min (m₁ x) (m₂ y) else 0)
      (fun b => m₂ b - if b = y then min (m₁ x) (m₂ y) else 0) < suppCard m₁ m₂ := by
  have s₁ : univ.filter (fun b => m₁ b - (if b = x then min (m₁ x) (m₂ y) else 0) ≠ 0) ⊆
      univ.filter (fun b => m₁ b ≠ 0) := by
    intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    by_cases hbx : b = x
    · rw [hbx]; exact hx.ne'
    · simpa [hbx] using hb
  have s₂ : univ.filter (fun b => m₂ b - (if b = y then min (m₁ x) (m₂ y) else 0) ≠ 0) ⊆
      univ.filter (fun b => m₂ b ≠ 0) := by
    intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    by_cases hby : b = y
    · rw [hby]; exact hy.ne'
    · simpa [hby] using hb
  simp only [suppCard]
  rcases min_choice (m₁ x) (m₂ y) with hm | hm
  · have hss := (ssubset_iff_of_subset s₁).mpr ⟨x, by simp [hx.ne'], by simp [hm]⟩
    have := card_lt_card hss
    have := card_le_card s₂
    omega
  · have hss := (ssubset_iff_of_subset s₂).mpr ⟨y, by simp [hy.ne'], by simp [hm]⟩
    have := card_lt_card hss
    have := card_le_card s₁
    omega

/-- **The coupling lemma.** Nonnegative masses of equal total, no candidate
    carrying more than the total of both together, have a coupling with no
    mass on the diagonal. -/
theorem offDiag_of_fits {m₁ m₂ : α → ℝ} {T : ℝ} (h : Fits m₁ m₂ T) : OffDiag m₁ m₂ := by
  have H : ∀ n, ∀ (m₁ m₂ : α → ℝ) (T : ℝ), suppCard m₁ m₂ = n → Fits m₁ m₂ T →
      OffDiag m₁ m₂ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro m₁ m₂ T hn h
      by_cases htight : ∃ a, m₁ a + m₂ a = T
      · obtain ⟨a, ha⟩ := htight
        exact offDiag_tight h a ha
      push Not at htight
      have hlt : ∀ b, m₁ b + m₂ b < T := fun b => lt_of_le_of_ne (h.le b) (htight b)
      by_cases hne : Nonempty α
      swap
      · have : IsEmpty α := not_nonempty_iff.mp hne
        exact ⟨fun _ _ => 0, fun x => isEmptyElim x, fun x => isEmptyElim x,
          fun x => isEmptyElim x, fun x => isEmptyElim x⟩
      obtain ⟨b₁⟩ := hne
      have hT : 0 < T := by linarith [hlt b₁, h.nonneg₁ b₁, h.nonneg₂ b₁]
      -- a row x and a column y ≠ x carrying mass
      obtain ⟨x, -, hx⟩ := exists_ne_zero_of_sum_ne_zero (h.sum₁.trans_ne hT.ne')
      have hx' : 0 < m₁ x := lt_of_le_of_ne (h.nonneg₁ x) (Ne.symm hx)
      have hs : ∑ y, (if y = x then 0 else m₂ y) ≠ 0 := by
        rw [sum_off, h.sum₂]
        exact (by linarith [hlt x] : 0 < T - m₂ x).ne'
      obtain ⟨y, -, hy⟩ := exists_ne_zero_of_sum_ne_zero hs
      have hyx : y ≠ x := by
        intro e
        simp [e] at hy
      have hy0 : m₂ y ≠ 0 := by
        intro e
        simp [hyx, e] at hy
      have hy' : 0 < m₂ y := lt_of_le_of_ne (h.nonneg₂ y) (Ne.symm hy0)
      have hxy : x ≠ y := hyx.symm
      by_cases hall : ∀ b, b ≠ x → b ≠ y → m₁ b + m₂ b ≤ T - min (m₁ x) (m₂ y)
      · -- move min (m₁ x) (m₂ y): a mass vanishes
        refine offDiag_add hxy (min (m₁ x) (m₂ y)) (le_min hx'.le hy'.le) ?_
        have hlt' := suppCard_lt hx' hy'
        rw [hn] at hlt'
        exact ih _ hlt' _ _ _ rfl (fits_sub h hxy (min_le_left _ _) (min_le_right _ _) hall)
      · -- move less, until a third candidate becomes tight
        push Not at hall
        obtain ⟨b₀, hb₀x, hb₀y, hb₀⟩ := hall
        obtain ⟨b, hbU, hbmax⟩ := (univ.filter (fun b => b ≠ x ∧ b ≠ y)).exists_max_image
          (fun b => m₁ b + m₂ b) ⟨b₀, by simp [hb₀x, hb₀y]⟩
        simp only [mem_filter, mem_univ, true_and] at hbU
        have hb₀le : m₁ b₀ + m₂ b₀ ≤ m₁ b + m₂ b := hbmax b₀ (by simp [hb₀x, hb₀y])
        have hmin1 := min_le_left (m₁ x) (m₂ y)
        have hmin2 := min_le_right (m₁ x) (m₂ y)
        refine offDiag_add hxy (T - (m₁ b + m₂ b)) (by linarith [hlt b]) ?_
        have hf := fits_sub h hxy (t := T - (m₁ b + m₂ b)) (by linarith) (by linarith)
          (fun b' hb'x hb'y => by
            have : m₁ b' + m₂ b' ≤ m₁ b + m₂ b := hbmax b' (by simp [hb'x, hb'y])
            linarith)
        refine offDiag_tight hf b ?_
        simp only [hbU.1, hbU.2, ↓reduceIte]
        ring
  exact H _ m₁ m₂ T rfl h

/-! ### Lemma 3 -/

/-- The part of the joint draw on the diagonal: X = Y = Z = x with mass d x. -/
def diagPart (d : α → ℝ) (x y z : α) : ℝ := if x = y then (if z = x then d x else 0) else 0

/-- The part off the diagonal: (X, Y) from Q, Z independently from l, rescaled by F. -/
noncomputable def offPart (Q : α → α → ℝ) (l : α → ℝ) (F : ℝ) (x y z : α) : ℝ :=
  Q x y * l z / F

lemma diag_sum₁ (d : α → ℝ) (x : α) : ∑ y, ∑ z, diagPart d x y z = d x := by
  rw [Fintype.sum_eq_single x (fun y hy => by simp [diagPart, Ne.symm hy])]
  simp [diagPart]

lemma diag_sum₂ (d : α → ℝ) (y : α) : ∑ x, ∑ z, diagPart d x y z = d y := by
  rw [Fintype.sum_eq_single y (fun x hx => by simp [diagPart, hx])]
  simp [diagPart]

lemma diag_sum₃ (d : α → ℝ) (z : α) : ∑ x, ∑ y, diagPart d x y z = d z := by
  rw [Fintype.sum_eq_single z (fun x hx => by simp [diagPart, Ne.symm hx])]
  simp [diagPart]

omit [DecidableEq α] in
/-- m · F / F = m, also when F = 0 forces m = 0. -/
lemma mul_div_self_of {m F : ℝ} (hm : F = 0 → m = 0) : m * F / F = m := by
  by_cases hF : F = 0
  · simp [hm hF, hF]
  · field_simp

omit [DecidableEq α] in
lemma eq_zero_of_sum {m : α → ℝ} (h0 : ∀ b, 0 ≤ m b) {F : ℝ} (hs : ∑ b, m b = F) (hF : F = 0)
    (b : α) : m b = 0 :=
  (sum_eq_zero_iff_of_nonneg (fun b _ => h0 b)).mp (hs.trans hF) b (mem_univ b)

omit [DecidableEq α] in
lemma off_sum₁ {Q : α → α → ℝ} {l : α → ℝ} {F : ℝ} (x : α) :
    ∑ y, ∑ z, offPart Q l F x y z = (∑ y, Q x y) * (∑ z, l z) / F := by
  unfold offPart
  rw [sum_mul_sum, sum_div]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_div]

omit [DecidableEq α] in
lemma off_sum₂ {Q : α → α → ℝ} {l : α → ℝ} {F : ℝ} (y : α) :
    ∑ x, ∑ z, offPart Q l F x y z = (∑ x, Q x y) * (∑ z, l z) / F := by
  unfold offPart
  rw [sum_mul_sum, sum_div]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_div]

omit [DecidableEq α] in
lemma off_sum₃ {Q : α → α → ℝ} {l : α → ℝ} {F : ℝ} (z : α) :
    ∑ x, ∑ y, offPart Q l F x y z = (∑ x, ∑ y, Q x y) * l z / F := by
  unfold offPart
  rw [sum_mul, sum_div]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_mul, sum_div]

/-- **Lemma 3, sufficient direction.** If λ(a) ≥ μ(a) + ν(a) − 1 for every
    candidate, the winners can be drawn jointly with X = Y ⇒ Z = X. -/
theorem lemma3_suff {μ ν lam : α → ℝ} (hμ0 : ∀ a, 0 ≤ μ a) (hν0 : ∀ a, 0 ≤ ν a)
    (hl0 : ∀ a, 0 ≤ lam a) (hμ1 : ∑ a, μ a = 1) (hν1 : ∑ a, ν a = 1) (hl1 : ∑ a, lam a = 1)
    (h : ∀ a, μ a + ν a - 1 ≤ lam a) : JoinLotteries.JointDraw3 μ ν lam := by
  -- pairs of candidates carry at most the total
  have pair : ∀ (m : α → ℝ), (∀ a, 0 ≤ m a) → ∑ a, m a = 1 → ∀ a b, a ≠ b → m a + m b ≤ 1 := by
    intro m h0 h1 a b hab
    have := sum_le_sum_of_subset_of_nonneg (subset_univ {a, b}) (fun i _ _ => h0 i)
    rw [sum_pair hab, h1] at this
    exact this
  have single : ∀ (m : α → ℝ), (∀ a, 0 ≤ m a) → ∑ a, m a = 1 → ∀ a, m a ≤ 1 := by
    intro m h0 h1 a
    have := single_le_sum (fun i _ => h0 i) (mem_univ a)
    rw [h1] at this
    exact this
  -- the mass on X = Y = Z
  let d : α → ℝ := fun a => max 0 (μ a + ν a - 1)
  have hd0 : ∀ a, 0 ≤ d a := fun a => le_max_left _ _
  have hdμ : ∀ a, d a ≤ μ a := fun a =>
    max_le (hμ0 a) (by linarith [single ν hν0 hν1 a])
  have hdν : ∀ a, d a ≤ ν a := fun a =>
    max_le (hν0 a) (by linarith [single μ hμ0 hμ1 a])
  have hdl : ∀ a, d a ≤ lam a := fun a => max_le (hl0 a) (h a)
  have hdge : ∀ a, μ a + ν a - 1 ≤ d a := fun a => le_max_right _ _
  have hdpos : ∀ a, 0 < d a → d a = μ a + ν a - 1 := by
    intro a ha
    rcases lt_max_iff.mp ha with h' | h'
    · exact absurd h' (lt_irrefl 0)
    · exact max_eq_right h'.le
  have huniq : ∀ a b, 0 < d a → 0 < d b → a = b := by
    intro a b ha hb
    by_contra hab
    have h1 := hdpos a ha
    have h2 := hdpos b hb
    have := pair μ hμ0 hμ1 a b hab
    have := pair ν hν0 hν1 a b hab
    linarith
  let D := ∑ a, d a
  let F := 1 - D
  -- the remaining masses fit
  have hfits : Fits (fun a => μ a - d a) (fun a => ν a - d a) F := by
    refine ⟨fun b => by show 0 ≤ μ b - d b; linarith [hdμ b],
      fun b => by show 0 ≤ ν b - d b; linarith [hdν b], ?_, ?_, fun b => ?_⟩
    · show ∑ a, (μ a - d a) = 1 - ∑ a, d a
      rw [sum_sub_distrib, hμ1]
    · show ∑ a, (ν a - d a) = 1 - ∑ a, d a
      rw [sum_sub_distrib, hν1]
    · show μ b - d b + (ν b - d b) ≤ 1 - ∑ a, d a
      by_cases hc : ∃ c, 0 < d c
      · obtain ⟨c, hc⟩ := hc
        have hD : ∑ a, d a = d c := Fintype.sum_eq_single c fun a ha => by
          by_contra hne
          exact ha (huniq a c (lt_of_le_of_ne (hd0 a) (Ne.symm hne)) hc)
        rw [hD]
        by_cases hbc : b = c
        · rw [hbc]
          linarith [hdge c]
        · have hdb : d b = 0 := by
            by_contra hne
            exact hbc (huniq b c (lt_of_le_of_ne (hd0 b) (Ne.symm hne)) hc)
          have h1 := hdpos c hc
          have := pair μ hμ0 hμ1 b c hbc
          have := pair ν hν0 hν1 b c hbc
          linarith
      · push Not at hc
        have hz : ∀ a, d a = 0 := fun a => le_antisymm (hc a) (hd0 a)
        have hD : ∑ a, d a = 0 := sum_eq_zero fun a _ => hz a
        rw [hD, hz b]
        linarith [hdge b, hz b]
  obtain ⟨Q, hQ0, hQr, hQc, hQd⟩ := offDiag_of_fits hfits
  let l : α → ℝ := fun a => lam a - d a
  have hl'0 : ∀ a, 0 ≤ l a := fun a => by linarith [hdl a]
  have hlsum : ∑ a, l a = F := by
    show ∑ a, (lam a - d a) = 1 - ∑ a, d a
    rw [sum_sub_distrib, hl1]
  have hF0 : 0 ≤ F := by
    rw [← hlsum]
    exact sum_nonneg fun a _ => hl'0 a
  have hQsum : ∑ x, ∑ y, Q x y = F := by
    rw [sum_congr rfl fun x _ => hQr x]
    exact hfits.sum₁
  refine ⟨fun x y z => diagPart d x y z + offPart Q l F x y z, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y z
    have h1 : 0 ≤ diagPart d x y z := by
      unfold diagPart
      split_ifs <;> first | exact le_refl 0 | exact hd0 x
    have h2 : 0 ≤ offPart Q l F x y z := div_nonneg (mul_nonneg (hQ0 x y) (hl'0 z)) hF0
    show 0 ≤ diagPart d x y z + offPart Q l F x y z
    linarith
  · intro x
    simp only [sum_add_distrib]
    rw [diag_sum₁, off_sum₁, hQr x, hlsum,
      mul_div_self_of (eq_zero_of_sum hfits.nonneg₁ hfits.sum₁ · x)]
    show d x + (μ x - d x) = μ x
    ring
  · intro y
    simp only [sum_add_distrib]
    rw [diag_sum₂, off_sum₂, hQc y, hlsum,
      mul_div_self_of (eq_zero_of_sum hfits.nonneg₂ hfits.sum₂ · y)]
    show d y + (ν y - d y) = ν y
    ring
  · intro z
    simp only [sum_add_distrib]
    rw [diag_sum₃, off_sum₃, hQsum, mul_comm F (l z),
      mul_div_self_of (eq_zero_of_sum hl'0 hlsum · z)]
    show d z + (lam z - d z) = lam z
    ring
  · intro x z hne
    by_contra hz
    apply hne
    simp [diagPart, offPart, hQd x, hz]

/-- **Lemma 3.** For lotteries μ, ν, λ, the winners can be drawn jointly with
    X = Y ⇒ Z = X exactly when λ(a) ≥ μ(a) + ν(a) − 1 for every candidate a. -/
theorem lemma3 {μ ν lam : α → ℝ} (hμ0 : ∀ a, 0 ≤ μ a) (hν0 : ∀ a, 0 ≤ ν a)
    (hl0 : ∀ a, 0 ≤ lam a) (hμ1 : ∑ a, μ a = 1) (hν1 : ∑ a, ν a = 1) (hl1 : ∑ a, lam a = 1) :
    JoinLotteries.JointDraw3 μ ν lam ↔ ∀ a, μ a + ν a - 1 ≤ lam a :=
  ⟨fun hj a => JoinLotteries.lemma3_nec hν1 hj a,
    lemma3_suff hμ0 hν0 hl0 hμ1 hν1 hl1⟩

/-! ### Monotone couplings on a chain

Strassen's theorem for a total order, the condition (E) of the reduction
proposition (*Consistency as an Extension Problem*, Section 3c). Candidates are
the positions 0, 1, …, n − 1 of a ranking, 0 the best. A lottery q
first-order stochastically dominates p when every top segment {0, …, k − 1}
has at least as much probability under q (`cum p k ≤ cum q k`). A monotone
coupling moves probability only upwards: J a b ≠ 0 implies b ≤ a.

The coupling is the quantile coupling: lay p and q out as consecutive
intervals of [0, T), best position first, and let J a b be the length of the
overlap of the interval of a under p with the interval of b under q (`ov`). -/

/-- The length of the overlap of [x₁, x₂) and [y₁, y₂). -/
noncomputable def ov (x₁ x₂ y₁ y₂ : ℝ) : ℝ := max 0 (min x₂ y₂ - max x₁ y₁)

lemma ov_nonneg (x₁ x₂ y₁ y₂ : ℝ) : 0 ≤ ov x₁ x₂ y₁ y₂ := le_max_left _ _

lemma ov_comm (x₁ x₂ y₁ y₂ : ℝ) : ov x₁ x₂ y₁ y₂ = ov y₁ y₂ x₁ x₂ := by
  unfold ov
  rw [min_comm x₂ y₂, max_comm x₁ y₁]

/-- Overlaps add over adjacent intervals. -/
lemma ov_add {x₁ x₂ a b c : ℝ} (hx : x₁ ≤ x₂) (hab : a ≤ b) (hbc : b ≤ c) :
    ov x₁ x₂ a b + ov x₁ x₂ b c = ov x₁ x₂ a c := by
  unfold ov
  simp only [max_def, min_def]
  split_ifs <;> linarith

lemma ov_self {x₁ x₂ : ℝ} (hx : x₁ ≤ x₂) (a : ℝ) : ov x₁ x₂ a a = 0 := by
  unfold ov
  simp only [max_def, min_def]
  split_ifs <;> linarith

lemma ov_full {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ ≤ x₂) (h1 : y₁ ≤ x₁) (h2 : x₂ ≤ y₂) :
    ov x₁ x₂ y₁ y₂ = x₂ - x₁ := by
  unfold ov
  simp only [max_def, min_def]
  split_ifs <;> linarith

lemma ov_zero_of {x₁ x₂ y₁ y₂ : ℝ} (h : min x₂ y₂ ≤ max x₁ y₁) : ov x₁ x₂ y₁ y₂ = 0 :=
  max_eq_left (sub_nonpos.mpr h)

/-- The intervals of a monotone sequence tile: the overlaps add up. -/
lemma ov_sum (y : ℕ → ℝ) (hy : Monotone y) {x₁ x₂ : ℝ} (hx : x₁ ≤ x₂) :
    ∀ n, ∑ b ∈ range n, ov x₁ x₂ (y b) (y (b + 1)) = ov x₁ x₂ (y 0) (y n)
  | 0 => by simp [ov_self hx]
  | n + 1 => by
    rw [sum_range_succ, ov_sum y hy hx n, ov_add hx (hy (Nat.zero_le n)) (hy (Nat.le_succ n))]

/-- The probability of the top k positions. -/
def cum (p : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ range k, p i

lemma cum_zero (p : ℕ → ℝ) : cum p 0 = 0 := by simp [cum]

lemma cum_succ (p : ℕ → ℝ) (k : ℕ) : cum p (k + 1) = cum p k + p k := sum_range_succ _ _

lemma cum_mono {p : ℕ → ℝ} (h0 : ∀ i, 0 ≤ p i) : Monotone (cum p) :=
  monotone_nat_of_le_succ fun k => by rw [cum_succ]; linarith [h0 k]

lemma cum_nonneg {p : ℕ → ℝ} (h0 : ∀ i, 0 ≤ p i) (k : ℕ) : 0 ≤ cum p k := by
  have := cum_mono h0 (Nat.zero_le k)
  rwa [cum_zero] at this

/-- A coupling of p and q on the positions below n that moves probability only
    upwards. -/
def MonoCoupling (n : ℕ) (p q : ℕ → ℝ) : Prop :=
  ∃ J : ℕ → ℕ → ℝ, (∀ a b, 0 ≤ J a b) ∧ (∀ a < n, ∑ b ∈ range n, J a b = p a) ∧
    (∀ b < n, ∑ a ∈ range n, J a b = q b) ∧ ∀ a b, J a b ≠ 0 → b ≤ a

/-- A monotone coupling makes q dominate p. -/
theorem dom_of_mono {n : ℕ} {p q : ℕ → ℝ} (h : MonoCoupling n p q) :
    ∀ k ≤ n, cum p k ≤ cum q k := by
  obtain ⟨J, h0, hr, hc, hs⟩ := h
  intro k hk
  unfold cum
  calc ∑ a ∈ range k, p a = ∑ a ∈ range k, ∑ b ∈ range n, J a b :=
        sum_congr rfl fun a ha => (hr a (lt_of_lt_of_le (mem_range.mp ha) hk)).symm
    _ = ∑ a ∈ range k, ∑ b ∈ range k, J a b := by
        refine sum_congr rfl fun a ha => ?_
        rw [← sum_range_add_sum_Ico _ hk]
        have hz : ∑ b ∈ Ico k n, J a b = 0 := by
          refine sum_eq_zero fun b hb => ?_
          by_contra hne
          have := hs a b hne
          have ha' := mem_range.mp ha
          have hb' := (mem_Ico.mp hb).1
          omega
        rw [hz, add_zero]
    _ ≤ ∑ a ∈ range n, ∑ b ∈ range k, J a b :=
        sum_le_sum_of_subset_of_nonneg (range_mono hk)
          (fun a _ _ => sum_nonneg fun b _ => h0 a b)
    _ = ∑ b ∈ range k, ∑ a ∈ range n, J a b := sum_comm
    _ = ∑ b ∈ range k, q b :=
        sum_congr rfl fun b hb => hc b (lt_of_lt_of_le (mem_range.mp hb) hk)

/-- **Strassen for a chain, sufficient direction.** If q dominates p and both
    have the same total on the positions below n, the quantile coupling is a
    monotone coupling. -/
theorem mono_of_dom {n : ℕ} {p q : ℕ → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (htot : cum p n = cum q n) (h : ∀ k ≤ n, cum p k ≤ cum q k) : MonoCoupling n p q := by
  have hP := cum_mono hp0
  have hQ := cum_mono hq0
  refine ⟨fun a b => if a < n ∧ b < n then
      ov (cum p a) (cum p (a + 1)) (cum q b) (cum q (b + 1)) else 0, ?_, ?_, ?_, ?_⟩
  · intro a b
    show 0 ≤ (if a < n ∧ b < n then ov (cum p a) (cum p (a + 1)) (cum q b) (cum q (b + 1)) else 0)
    split_ifs
    · exact ov_nonneg _ _ _ _
    · exact le_refl 0
  · intro a ha
    show ∑ b ∈ range n, (if a < n ∧ b < n then
      ov (cum p a) (cum p (a + 1)) (cum q b) (cum q (b + 1)) else 0) = p a
    have e : ∑ b ∈ range n, (if a < n ∧ b < n then
        ov (cum p a) (cum p (a + 1)) (cum q b) (cum q (b + 1)) else 0) =
        ∑ b ∈ range n, ov (cum p a) (cum p (a + 1)) (cum q b) (cum q (b + 1)) :=
      sum_congr rfl fun b hb => by rw [ite_eq_left ⟨ha, mem_range.mp hb⟩]
    rw [e]
    have hx : cum p a ≤ cum p (a + 1) := hP (Nat.le_succ a)
    rw [ov_sum (cum q) hQ hx n, ov_full hx (by rw [cum_zero]; exact cum_nonneg hp0 a)
      (by rw [← htot]; exact hP (by omega)), cum_succ]
    ring
  · intro b hb
    show ∑ a ∈ range n, (if a < n ∧ b < n then
      ov (cum p a) (cum p (a + 1)) (cum q b) (cum q (b + 1)) else 0) = q b
    have e : ∑ a ∈ range n, (if a < n ∧ b < n then
        ov (cum p a) (cum p (a + 1)) (cum q b) (cum q (b + 1)) else 0) =
        ∑ a ∈ range n, ov (cum q b) (cum q (b + 1)) (cum p a) (cum p (a + 1)) :=
      sum_congr rfl fun a ha => by rw [ite_eq_left ⟨mem_range.mp ha, hb⟩, ov_comm]
    rw [e]
    have hx : cum q b ≤ cum q (b + 1) := hQ (Nat.le_succ b)
    rw [ov_sum (cum p) hP hx n, ov_full hx (by rw [cum_zero]; exact cum_nonneg hq0 b)
      (by rw [htot]; exact hQ (by omega)), cum_succ]
    ring
  · intro a b hne
    by_contra hba
    apply hne
    show (if a < n ∧ b < n then
      ov (cum p a) (cum p (a + 1)) (cum q b) (cum q (b + 1)) else 0) = 0
    split_ifs with hab
    · apply ov_zero_of
      have h1 : cum p (a + 1) ≤ cum q (a + 1) := h (a + 1) (by omega)
      have h2 : cum q (a + 1) ≤ cum q b := hQ (by omega)
      calc min (cum p (a + 1)) (cum q (b + 1)) ≤ cum p (a + 1) := min_le_left _ _
        _ ≤ cum q b := h1.trans h2
        _ ≤ max (cum p a) (cum q b) := le_max_right _ _
    · rfl

/-- **Strassen for a chain.** For nonnegative p and q of equal total on the
    positions below n, a monotone coupling exists exactly when q dominates p. -/
theorem mono_iff_dom {n : ℕ} {p q : ℕ → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (htot : cum p n = cum q n) : MonoCoupling n p q ↔ ∀ k ≤ n, cum p k ≤ cum q k :=
  ⟨dom_of_mono, mono_of_dom hp0 hq0 htot⟩

end Couplings

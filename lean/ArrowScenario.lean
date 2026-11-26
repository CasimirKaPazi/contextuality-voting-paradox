/-
  Arrow's scenario as an instance of the frame of `Scenarios.lean`
  (*Four Levels of Obstruction in Social Choice*, Section 5), and Theorem 5′
  as a statement about the frame.

  The scenario (`scen`), for voters ι and alternatives α:
  * a variable is an ordered pair (x, y) of alternatives with a column, the
    bits of the voters on that pair (`Var`); its value is the social bit,
    whether x is placed above y;
  * the context of a profile π holds, for each pair x ≠ y, the variable with
    π's column on it (`ctxOf`). Two profiles share a variable when they agree
    on a pair, so requiring one value per variable is independence of
    irrelevant alternatives;
  * the admissible assignments on the context of π are the restrictions of
    social rankings σ respecting unanimity at π (`locOf`, `Unan`). The bits of
    (x, y) and (y, x) are complementary because they come from one ranking.

  Bridge with `ArrowGeneral.lean`, where a model is a lottery over social
  rankings at every profile:
  * `model_eOf`: every `ArrowGeneral.Model` gives an empirical model of the
    scenario (`eOf`);
  * `model_μOf`: every empirical model of the scenario gives an
    `ArrowGeneral.Model` (`μOf`), and `e_eq` recovers the empirical model
    from it; `μOf_eOf` is the other round trip.
  Full compatibility in the frame (equal marginals on shared variables) is
  exactly full compatibility in `ArrowGeneral.Model` (events determined by a
  set of pairs on which two profiles agree).

  * `dict_global`: the dictatorships are global sections.
  * `noncontextual` (Theorem 5′ in the frame): with at least three
    alternatives every empirical model is non-contextual; the hidden variable
    is a dictator, drawn with the weights of `ArrowBase.theorem5'`.
  * `global_dict` (Arrow's theorem, from Theorem 5′): every global section
    agrees with one dictatorship on every context.
  * `voters`: the permutations of the voters as a symmetry of the scenario,
    acting on the columns.
  * `level3`: with at least three alternatives and two voters the scenario is
    at level 3, and `division_voters` gives random dictatorship as a symmetric,
    non-contextual model without symmetric global section.
-/

module

public import ArrowBase
public import Scenarios

@[expose] public section

open Finset PathPinning Scenarios

namespace ArrowScenario

/-- A variable: an ordered pair of alternatives and a column of voters' bits. -/
abbrev Var (ι α : Type*) := (α × α) × (ι → Bool)

section Defs

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- The column of π on the pair (x, y): which voters rank x above y. -/
def col (π : ι → Rk α) (x y : α) : ι → Bool := fun k => (π k).1 x y

/-- The context of a profile: for each pair x ≠ y, the variable with π's column. -/
def ctxOf (π : ι → Rk α) : Finset (Var ι α) :=
  (univ.filter (fun p : α × α => p.1 ≠ p.2)).image (fun p => (p, col π p.1 p.2))

/-- A social ranking read as a global assignment: the bit of (x, y) is σ's. -/
def glob (σ : Rk α) : Var ι α → Bool := fun v => σ.1 v.1.1 v.1.2

/-- The local assignment of σ on the context of π. -/
def locOf (π : ι → Rk α) (σ : Rk α) : Loc (Var ι α) Bool := ofGlobal (ctxOf π) (glob σ)

/-- σ respects unanimity at π. -/
def Unan (π : ι → Rk α) (σ : Rk α) : Prop :=
  ∀ x y, (∀ k, (π k).1 x y = true) → σ.1 x y = true

/-- Arrow's scenario. -/
noncomputable def scen : Scenario (Var ι α) Bool where
  ctx := univ.image ctxOf
  adm c ρ := ∃ π σ, c = ctxOf π ∧ ρ = locOf π σ ∧ Unan π σ

/-- The global assignment of dictator k: the social bit is k's bit. -/
def dict (k : ι) : Var ι α → Bool := fun v => v.2 k

end Defs

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-! ### Contexts and local assignments -/

omit [DecidableEq ι] in
lemma mem_ctxOf_iff (π : ι → Rk α) (v : Var ι α) :
    v ∈ ctxOf π ↔ v.1.1 ≠ v.1.2 ∧ v.2 = col π v.1.1 v.1.2 := by
  unfold ctxOf
  rw [mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(mem_filter.mp hp).2, rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨v.1, mem_filter.mpr ⟨mem_univ _, h1⟩, Prod.ext rfl h2.symm⟩

lemma mem_ctx (π : ι → Rk α) : ctxOf π ∈ (scen : Scenario (Var ι α) Bool).ctx :=
  mem_image_of_mem ctxOf (mem_univ π)

omit [DecidableEq ι] in
/-- Different profiles have different contexts. -/
lemma ctxOf_inj : Function.Injective (ctxOf (ι := ι) (α := α)) := by
  intro π π' h
  funext k
  apply Subtype.ext
  funext x y
  by_cases hxy : x = y
  · subst hxy
    rw [PathPinning.irrefl, PathPinning.irrefl]
  · have hm : ((x, y), col π x y) ∈ ctxOf π' := h ▸ (mem_ctxOf_iff π _).mpr ⟨hxy, rfl⟩
    exact congrFun ((mem_ctxOf_iff π' _).mp hm).2 k

omit [DecidableEq ι] in
/-- On one context, different rankings have different local assignments. -/
lemma locOf_inj (π : ι → Rk α) : Function.Injective (locOf π) := by
  intro σ σ' h
  apply Subtype.ext
  funext x y
  by_cases hxy : x = y
  · subst hxy
    rw [PathPinning.irrefl, PathPinning.irrefl]
  · have hv : ((x, y), col π x y) ∈ ctxOf π := (mem_ctxOf_iff π _).mpr ⟨hxy, rfl⟩
    have := congrFun h ((x, y), col π x y)
    simp only [locOf, ofGlobal, hv, ↓reduceIte, Option.some.injEq, glob] at this
    exact this

omit [DecidableEq ι] in
lemma restr_loc (π : ι → Rk α) {T : Finset (Var ι α)} (hT : T ⊆ ctxOf π) (σ : Rk α) :
    restr T (locOf π σ) = ofGlobal T (glob σ) := by
  rw [locOf, restr_ofGlobal, inter_eq_left.mpr hT]

/-! ### Sums over fibres -/

lemma sum_sum_filter {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B] (h : A → B)
    (P : B → Prop) [DecidablePred P] (w : A → ℝ) :
    ∑ b ∈ univ.filter P, ∑ a ∈ univ.filter (fun a => h a = b), w a =
      ∑ a ∈ univ.filter (fun a => P (h a)), w a := by
  rw [← sum_fiberwise_of_maps_to (s := univ.filter (fun a => P (h a))) (t := univ.filter P)
    (g := h) (f := w) (fun a ha => by simpa using ha)]
  apply sum_congr rfl
  intro b hb
  apply sum_congr _ (fun _ _ => rfl)
  ext a
  simp only [mem_filter, mem_univ, true_and] at hb ⊢
  constructor
  · intro hab
    exact ⟨by rw [hab]; exact hb, hab⟩
  · exact fun h' => h'.2

/-- A sum over an event that is constant on the fibres of r, taken fibre by fibre. -/
lemma sum_fibers {f : Rk α → ℝ} {E : Rk α → Bool} {r : Rk α → Loc (Var ι α) Bool}
    (hconst : ∀ σ σ', r σ = r σ' → E σ = E σ') :
    ∑ σ ∈ univ.filter (fun σ => E σ = true), f σ =
      ∑ τ ∈ (univ.filter (fun σ => E σ = true)).image r,
        ∑ σ ∈ univ.filter (fun σ => r σ = τ), f σ := by
  rw [← sum_fiberwise_of_maps_to (s := univ.filter (fun σ => E σ = true))
    (t := (univ.filter (fun σ => E σ = true)).image r) (g := r) (f := f)
    (fun σ hσ => mem_image_of_mem r hσ)]
  apply sum_congr rfl
  intro τ hτ
  obtain ⟨σ₀, hσ₀, rfl⟩ := mem_image.mp hτ
  apply sum_congr _ (fun _ _ => rfl)
  ext σ
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨(hconst σ σ₀ h).trans (mem_filter.mp hσ₀).2, h⟩

/-! ### From lotteries over rankings to the frame -/

/-- The empirical model of a family of lotteries over social rankings. -/
noncomputable def eOf (μ : (ι → Rk α) → Rk α → ℝ) (c : Finset (Var ι α))
    (ρ : Loc (Var ι α) Bool) : ℝ :=
  ∑ π ∈ univ.filter (fun π => ctxOf π = c), ∑ σ ∈ univ.filter (fun σ => locOf π σ = ρ), μ π σ

/-- The lotteries over social rankings of a family of context distributions. -/
def μOf (e : Finset (Var ι α) → Loc (Var ι α) Bool → ℝ) (π : ι → Rk α) (σ : Rk α) : ℝ :=
  e (ctxOf π) (locOf π σ)

lemma eOf_ctxOf (μ : (ι → Rk α) → Rk α → ℝ) (π : ι → Rk α) (ρ : Loc (Var ι α) Bool) :
    eOf μ (ctxOf π) ρ = ∑ σ ∈ univ.filter (fun σ => locOf π σ = ρ), μ π σ := by
  unfold eOf
  have : univ.filter (fun π' => ctxOf π' = ctxOf π) = {π} := by
    ext π'
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun h => ctxOf_inj h, fun h => h ▸ rfl⟩
  rw [this, sum_singleton]

theorem μOf_eOf (μ : (ι → Rk α) → Rk α → ℝ) : μOf (eOf μ) = μ := by
  funext π σ
  unfold μOf
  rw [eOf_ctxOf]
  have : univ.filter (fun σ' => locOf π σ' = locOf π σ) = {σ} := by
    ext σ'
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact (locOf_inj π).eq_iff
  rw [this, sum_singleton]

lemma eOf_total (μ : (ι → Rk α) → Rk α → ℝ) (π : ι → Rk α) :
    ∑ ρ, eOf μ (ctxOf π) ρ = ∑ σ, μ π σ := by
  simp_rw [eOf_ctxOf]
  exact sum_fiberwise univ (locOf π) (μ π)

lemma marg_eOf (μ : (ι → Rk α) → Rk α → ℝ) (π : ι → Rk α) {T : Finset (Var ι α)}
    (hT : T ⊆ ctxOf π) (τ : Loc (Var ι α) Bool) :
    marg (eOf μ (ctxOf π)) T τ =
      ∑ σ ∈ univ.filter (fun σ => ofGlobal T (glob σ) = τ), μ π σ := by
  unfold marg
  simp_rw [eOf_ctxOf]
  rw [sum_comm' (t' := univ.filter (fun σ => restr T (locOf π σ) = τ))
    (s' := fun σ => {locOf π σ})]
  · simp only [sum_singleton, restr_loc π hT]
  · intro ρ σ
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨h1, rfl⟩; exact ⟨rfl, h1⟩
    · rintro ⟨rfl, h2⟩; exact ⟨h2, rfl⟩

omit [Fintype ι] [DecidableEq ι] in
/-- A ranking with positive probability respects unanimity. -/
lemma unan_of_ne {μ : (ι → Rk α) → Rk α → ℝ} (hM : ArrowGeneral.Model μ) {π : ι → Rk α}
    {σ : Rk α} (h : μ π σ ≠ 0) : Unan π σ := by
  intro x y hxy
  by_contra hne
  have h1 := hM.unan π x y hxy
  have h2 := hM.total π
  have hs := sum_filter_add_sum_filter_not univ (fun σ' : Rk α => σ'.1 x y = true) (μ π)
  change ∑ σ' ∈ univ.filter (fun σ' : Rk α => σ'.1 x y = true), μ π σ' = 1 at h1
  have hz : ∑ σ' ∈ univ.filter (fun σ' : Rk α => ¬ σ'.1 x y = true), μ π σ' = 0 := by
    linarith
  exact h ((sum_eq_zero_iff_of_nonneg (fun σ' _ => hM.nonneg π σ')).mp hz σ
    (mem_filter.mpr ⟨mem_univ _, hne⟩))

/-- Every model of `ArrowGeneral.lean` is an empirical model of the scenario. -/
theorem model_eOf {μ : (ι → Rk α) → Rk α → ℝ} (hM : ArrowGeneral.Model μ) :
    Scenarios.Model scen (eOf μ) where
  nonneg c ρ := sum_nonneg fun π _ => sum_nonneg fun σ _ => hM.nonneg π σ
  total c hc := by
    obtain ⟨π, -, rfl⟩ := mem_image.mp hc
    rw [eOf_total, hM.total]
  supp c hc ρ hρ := by
    obtain ⟨π, -, rfl⟩ := mem_image.mp hc
    rw [eOf_ctxOf] at hρ
    obtain ⟨σ, hσ, hμ⟩ := exists_ne_zero_of_sum_ne_zero hρ
    have hσ' : locOf π σ = ρ := (mem_filter.mp hσ).2
    exact ⟨⟨π, σ, rfl, hσ'.symm, unan_of_ne hM hμ⟩, glob σ, hσ'.symm⟩
  compat c hc c' hc' τ := by
    obtain ⟨π, -, rfl⟩ := mem_image.mp hc
    obtain ⟨π', -, rfl⟩ := mem_image.mp hc'
    rw [marg_eOf μ π inter_subset_left, marg_eOf μ π' inter_subset_right]
    have hdet : ArrowGeneral.Det ((ctxOf π ∩ ctxOf π').image Prod.fst)
        (fun σ => decide (ofGlobal (ctxOf π ∩ ctxOf π') (glob σ) = τ)) := by
      intro σ σ' hag
      have : ofGlobal (ctxOf π ∩ ctxOf π') (glob σ) = ofGlobal (ctxOf π ∩ ctxOf π') (glob σ') := by
        funext v
        by_cases hv : v ∈ ctxOf π ∩ ctxOf π'
        · simp only [ofGlobal, hv, ↓reduceIte]
          exact congrArg some (hag v.1 (mem_image_of_mem Prod.fst hv))
        · simp only [ofGlobal, hv, ↓reduceIte]
      simp only [this]
    have hagr : ArrowGeneral.AgreeP ((ctxOf π ∩ ctxOf π').image Prod.fst) π π' := by
      intro k p hp
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hp
      have h1 := ((mem_ctxOf_iff π v).mp (mem_inter.mp hv).1).2
      have h2 := ((mem_ctxOf_iff π' v).mp (mem_inter.mp hv).2).2
      exact congrFun (h1.symm.trans h2) k
    have := hM.compat _ _ hdet π π' hagr
    simpa only [ArrowGeneral.prob, decide_eq_true_eq] using this

/-! ### From the frame to lotteries over rankings -/

section FromFrame

variable {e : Finset (Var ι α) → Loc (Var ι α) Bool → ℝ}

lemma e_zero (he : Scenarios.Model scen e) (π : ι → Rk α) (ρ : Loc (Var ι α) Bool)
    (hρ : ∀ σ, locOf π σ ≠ ρ) : e (ctxOf π) ρ = 0 := by
  by_contra h
  obtain ⟨⟨π', σ, hc, hρ', -⟩, -⟩ := he.supp (ctxOf π) (mem_ctx π) ρ h
  have hπ := ctxOf_inj hc
  subst hπ
  exact hρ σ hρ'.symm

/-- An empirical model of the scenario is determined by its lotteries over rankings. -/
lemma e_eq (he : Scenarios.Model scen e) (π : ι → Rk α) (ρ : Loc (Var ι α) Bool) :
    e (ctxOf π) ρ = eOf (μOf e) (ctxOf π) ρ := by
  rw [eOf_ctxOf]
  by_cases h : ∃ σ, locOf π σ = ρ
  · obtain ⟨σ₀, rfl⟩ := h
    have : univ.filter (fun σ => locOf π σ = locOf π σ₀) = {σ₀} := by
      ext σ
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact (locOf_inj π).eq_iff
    rw [this, sum_singleton]
    rfl
  · push Not at h
    rw [e_zero he π ρ h]
    symm
    apply sum_eq_zero
    intro σ hσ
    exact absurd (mem_filter.mp hσ).2 (h σ)

lemma total_μOf (he : Scenarios.Model scen e) (π : ι → Rk α) : ∑ σ, μOf e π σ = 1 := by
  rw [← eOf_total (μOf e) π, ← he.total (ctxOf π) (mem_ctx π)]
  exact sum_congr rfl fun ρ _ => (e_eq he π ρ).symm

lemma unan_of_ne_e (he : Scenarios.Model scen e) {π : ι → Rk α} {σ : Rk α}
    (h : μOf e π σ ≠ 0) : Unan π σ := by
  obtain ⟨⟨π', σ', hc, hρ, hu⟩, -⟩ := he.supp (ctxOf π) (mem_ctx π) (locOf π σ) h
  have hπ := ctxOf_inj hc
  subst hπ
  have hσ := locOf_inj π hρ
  subst hσ
  exact hu

lemma marg_e (he : Scenarios.Model scen e) (π : ι → Rk α) {T : Finset (Var ι α)}
    (hT : T ⊆ ctxOf π) (τ : Loc (Var ι α) Bool) :
    marg (e (ctxOf π)) T τ = ∑ σ ∈ univ.filter (fun σ => ofGlobal T (glob σ) = τ), μOf e π σ := by
  have : e (ctxOf π) = eOf (μOf e) (ctxOf π) := funext (e_eq he π)
  rw [this, marg_eOf _ π hT]

/-- Every empirical model of the scenario is a model of `ArrowGeneral.lean`. -/
theorem model_μOf (he : Scenarios.Model scen e) : ArrowGeneral.Model (μOf e) where
  nonneg π σ := he.nonneg _ _
  total := total_μOf he
  compat S E hE π π' hag := by
    have hconst : ∀ σ σ', ofGlobal (ctxOf π ∩ ctxOf π') (glob σ) =
        ofGlobal (ctxOf π ∩ ctxOf π') (glob σ') → E σ = E σ' := by
      intro σ σ' h
      apply hE σ σ'
      intro p hp
      by_cases hp' : p.1 = p.2
      · rw [hp', PathPinning.irrefl, PathPinning.irrefl]
      · have hv : (p, col π p.1 p.2) ∈ ctxOf π ∩ ctxOf π' :=
          mem_inter.mpr ⟨(mem_ctxOf_iff π _).mpr ⟨hp', rfl⟩,
            (mem_ctxOf_iff π' _).mpr ⟨hp', funext fun k => hag k p hp⟩⟩
        have := congrFun h (p, col π p.1 p.2)
        simp only [ofGlobal, hv, ↓reduceIte, Option.some.injEq, glob] at this
        exact this
    unfold ArrowGeneral.prob
    rw [sum_fibers (f := μOf e π) (E := E)
        (r := fun σ => ofGlobal (ctxOf π ∩ ctxOf π') (glob σ)) hconst,
      sum_fibers (f := μOf e π') (E := E)
        (r := fun σ => ofGlobal (ctxOf π ∩ ctxOf π') (glob σ)) hconst]
    apply sum_congr rfl
    intro τ _
    have h1 := marg_e he π (inter_subset_left : ctxOf π ∩ ctxOf π' ⊆ ctxOf π) τ
    have h2 := marg_e he π' (inter_subset_right : ctxOf π ∩ ctxOf π' ⊆ ctxOf π') τ
    have h3 := he.compat _ (mem_ctx π) _ (mem_ctx π') τ
    rw [h1, h2] at h3
    exact h3
  unan π x y hxy := by
    have hz : ∑ σ ∈ univ.filter (fun σ : Rk α => ¬ σ.1 x y = true), μOf e π σ = 0 := by
      apply sum_eq_zero
      intro σ hσ
      by_contra h
      exact (mem_filter.mp hσ).2 (unan_of_ne_e he h x y hxy)
    have hs := sum_filter_add_sum_filter_not univ (fun σ : Rk α => σ.1 x y = true) (μOf e π)
    have ht := total_μOf he π
    show ∑ σ ∈ univ.filter (fun σ : Rk α => σ.1 x y = true), μOf e π σ = 1
    linarith

end FromFrame

/-! ### Dictatorships and Theorem 5′ in the frame -/

omit [DecidableEq ι] in
lemma dict_loc (π : ι → Rk α) (k : ι) : ofGlobal (ctxOf π) (dict k) = locOf π (π k) := by
  funext v
  by_cases hv : v ∈ ctxOf π
  · simp only [locOf, ofGlobal, hv, ↓reduceIte]
    exact congrArg some (congrFun ((mem_ctxOf_iff π v).mp hv).2 k)
  · simp only [locOf, ofGlobal, hv, ↓reduceIte]

/-- The dictatorships are global sections. -/
theorem dict_global (k : ι) : IsGlobal (scen : Scenario (Var ι α) Bool) (dict k) := by
  intro c hc
  obtain ⟨π, -, rfl⟩ := mem_image.mp hc
  exact ⟨π, π k, rfl, dict_loc π k, fun x y h => h k⟩

/-- **Theorem 5′ in the frame.** With at least three alternatives, every
    empirical model of Arrow's scenario is non-contextual: it is induced by a
    distribution on the dictatorships. -/
theorem noncontextual (hα : 3 ≤ Fintype.card α) {e : Finset (Var ι α) → Loc (Var ι α) Bool → ℝ}
    (he : Scenarios.Model scen e) : NonContextual scen e := by
  obtain ⟨w, hw0, hw1, hmix⟩ := ArrowBase.theorem5' α hα (μOf e) (model_μOf he)
  refine ⟨fun f => ∑ k ∈ univ.filter (fun k => dict k = f), w k,
    fun f => sum_nonneg fun k _ => hw0 k, ?_, ?_, ?_⟩
  · show ∑ f, ∑ k ∈ univ.filter (fun k => dict k = f), w k = 1
    rw [sum_fiberwise univ dict w, hw1]
  · intro f hf
    have hf' : ∑ k ∈ univ.filter (fun k => dict k = f), w k ≠ 0 := hf
    obtain ⟨k, hk, -⟩ := exists_ne_zero_of_sum_ne_zero hf'
    have hkf : dict k = f := (mem_filter.mp hk).2
    subst hkf
    exact dict_global k
  · intro c hc ρ
    obtain ⟨π, -, rfl⟩ := mem_image.mp hc
    rw [e_eq he π ρ, eOf_ctxOf]
    simp_rw [hmix π]
    rw [sum_sum_filter π (fun σ => locOf π σ = ρ) w]
    simp only [mix]
    rw [sum_sum_filter dict (fun f => ofGlobal (ctxOf π) f = ρ) w]
    simp_rw [dict_loc]

/-! ### Arrow's theorem from Theorem 5′ -/

/-- The distribution concentrated on one global assignment. -/
noncomputable def point (f : Var ι α → Bool) : (Var ι α → Bool) → ℝ :=
  fun f' => if f' = f then 1 else 0

/-- **Arrow's theorem in the frame.** With at least three alternatives, every
    global section agrees with one dictatorship on every context. It is a
    deterministic empirical model, so by Theorem 5′ a mixture of
    dictatorships, and any voter of positive weight decides at every profile. -/
theorem global_dict (hα : 3 ≤ Fintype.card α) {f : Var ι α → Bool}
    (hf : IsGlobal (scen : Scenario (Var ι α) Bool) f) :
    ∃ k, ∀ π, ofGlobal (ctxOf π) f = ofGlobal (ctxOf π) (dict k) := by
  have h0 : ∀ f', 0 ≤ point f f' := fun f' => by
    unfold point; split_ifs <;> norm_num
  have h1 : ∑ f', point f f' = 1 := by simp [point]
  have hg : ∀ f', point f f' ≠ 0 → IsGlobal (scen : Scenario (Var ι α) Bool) f' := by
    intro f' h
    unfold point at h
    split_ifs at h with hf'
    · rw [hf']; exact hf
    · exact absurd rfl h
  have hm := Scenarios.mix_model (scen : Scenario (Var ι α) Bool) h0 h1 hg
  obtain ⟨w, hw0, hw1, hmix⟩ := ArrowBase.theorem5' α hα (μOf (mix (point f))) (model_μOf hm)
  obtain ⟨k, -, hk⟩ := exists_ne_zero_of_sum_ne_zero (by rw [hw1]; norm_num : ∑ k, w k ≠ 0)
  refine ⟨k, fun π => ?_⟩
  have hpos : μOf (mix (point f)) π (π k) ≠ 0 := by
    rw [hmix]
    have hle : w k ≤ ∑ j ∈ univ.filter (fun j => π j = π k), w j :=
      single_le_sum (fun j _ => hw0 j) (mem_filter.mpr ⟨mem_univ _, rfl⟩)
    have hlt : 0 < w k := lt_of_le_of_ne (hw0 k) (Ne.symm hk)
    exact (lt_of_lt_of_le hlt hle).ne'
  unfold μOf mix at hpos
  obtain ⟨f', hf', hd⟩ := exists_ne_zero_of_sum_ne_zero hpos
  have hf'f : f' = f := by
    by_contra h
    exact hd (by simp [point, h])
  rw [dict_loc, ← hf'f]
  exact (mem_filter.mp hf').2

/-! ### The voters' permutations -/

/-- A permutation of the voters acts on a variable through its column. -/
def actV (g : Equiv.Perm ι) (v : Var ι α) : Var ι α := (v.1, fun k => v.2 (g⁻¹ k))

/-- A permutation of the voters acts on a profile. -/
def actP (g : Equiv.Perm ι) (π : ι → Rk α) : ι → Rk α := fun k => π (g⁻¹ k)

omit [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] in
lemma actV_mul (g h : Equiv.Perm ι) (v : Var ι α) : actV (g * h) v = actV g (actV h v) := by
  simp [actV, mul_inv_rev]

omit [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] in
lemma actV_one (v : Var ι α) : actV 1 v = v := by
  simp [actV]

omit [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] in
lemma actV_inv_actV (g : Equiv.Perm ι) (v : Var ι α) : actV g⁻¹ (actV g v) = v := by
  rw [← actV_mul, inv_mul_cancel, actV_one]

omit [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] in
lemma actV_actV_inv (g : Equiv.Perm ι) (v : Var ι α) : actV g (actV g⁻¹ v) = v := by
  rw [← actV_mul, mul_inv_cancel, actV_one]

omit [DecidableEq ι] [Fintype α] in
lemma mem_image_actV {c : Finset (Var ι α)} {g : Equiv.Perm ι} {v : Var ι α} :
    v ∈ c.image (actV g) ↔ actV g⁻¹ v ∈ c := by
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hv
    rwa [actV_inv_actV]
  · intro h
    exact mem_image.mpr ⟨_, h, actV_actV_inv g v⟩

omit [DecidableEq ι] in
lemma ctxOf_act (g : Equiv.Perm ι) (π : ι → Rk α) :
    ctxOf (actP g π) = (ctxOf π).image (actV g) := by
  ext v
  rw [mem_image_actV, mem_ctxOf_iff, mem_ctxOf_iff]
  show v.1.1 ≠ v.1.2 ∧ v.2 = col (actP g π) v.1.1 v.1.2 ↔
    v.1.1 ≠ v.1.2 ∧ (fun k => v.2 (g⁻¹⁻¹ k)) = col π v.1.1 v.1.2
  rw [inv_inv]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, funext fun k => ?_⟩
    rw [h2]
    simp [col, actP]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, funext fun k => ?_⟩
    have := congrFun h2 (g⁻¹ k)
    simpa [col, actP] using this

/-- The action on contexts. -/
def onCf (g : Equiv.Perm ι) (c : Finset (Var ι α)) : Finset (Var ι α) := c.image (actV g)

/-- The action on global assignments. -/
def onAf (g : Equiv.Perm ι) (f : Var ι α → Bool) : Var ι α → Bool := fun v => f (actV g⁻¹ v)

/-- The action on local assignments. -/
def onLf (g : Equiv.Perm ι) (ρ : Loc (Var ι α) Bool) : Loc (Var ι α) Bool :=
  fun v => ρ (actV g⁻¹ v)

omit [DecidableEq ι] [Fintype α] in
lemma res_act (g : Equiv.Perm ι) (c : Finset (Var ι α)) (f : Var ι α → Bool) :
    ofGlobal (onCf g c) (onAf g f) = onLf g (ofGlobal c f) := by
  funext v
  simp only [ofGlobal, onCf, onAf, onLf, mem_image_actV]

omit [DecidableEq ι] in
lemma locOf_act (g : Equiv.Perm ι) (π : ι → Rk α) (σ : Rk α) :
    onLf g (locOf π σ) = locOf (actP g π) σ := by
  rw [locOf, ← res_act, locOf, ctxOf_act]
  rfl

omit [Fintype ι] [DecidableEq ι] in
lemma unan_act (g : Equiv.Perm ι) (π : ι → Rk α) (σ : Rk α) :
    Unan (actP g π) σ ↔ Unan π σ := by
  constructor
  · intro h x y hxy
    exact h x y fun k => hxy (g⁻¹ k)
  · intro h x y hxy
    refine h x y fun k => ?_
    have := hxy (g k)
    simpa [actP] using this

/-- The permutations of the voters as a symmetry of Arrow's scenario. -/
noncomputable def voters : Symmetry (scen : Scenario (Var ι α) Bool) (Equiv.Perm ι) where
  onC := onCf
  onA := onAf
  onL := onLf
  onC_mul g h c := by
    unfold onCf
    rw [image_image]
    exact congrArg (fun f => c.image f) (funext fun v => actV_mul g h v)
  onC_one c := by
    unfold onCf
    have : actV (1 : Equiv.Perm ι) = (id : Var ι α → Var ι α) := funext actV_one
    rw [this, image_id]
  onA_mul g h f := by
    funext v
    simp only [onAf]
    rw [mul_inv_rev, actV_mul]
  onL_inj g ρ ρ' h := by
    funext v
    have := congrFun h (actV g v)
    simpa [onLf, actV_inv_actV] using this
  ctx_mem g c hc := by
    obtain ⟨π, -, rfl⟩ := mem_image.mp hc
    show (ctxOf π).image (actV g) ∈ _
    rw [← ctxOf_act]
    exact mem_ctx _
  adm_iff g c ρ := by
    constructor
    · rintro ⟨π, σ, hc, hρ, hu⟩
      refine ⟨actP g⁻¹ π, σ, ?_, ?_, (unan_act g⁻¹ π σ).mpr hu⟩
      · rw [ctxOf_act, ← hc]
        ext v
        rw [onCf, mem_image_actV, mem_image_actV, inv_inv, actV_inv_actV]
      · rw [← locOf_act, ← hρ]
        funext v
        simp only [onLf, inv_inv, actV_inv_actV]
    · rintro ⟨π, σ, rfl, rfl, hu⟩
      exact ⟨actP g π, σ, (ctxOf_act g π).symm, locOf_act g π σ, (unan_act g π σ).mpr hu⟩
  res := res_act

omit [DecidableEq ι] in
/-- At a profile, the social bit of a variable of the context is the dictator's bit. -/
lemma bit_of_dict {f : Var ι α → Bool} {k : ι}
    (hk : ∀ π, ofGlobal (ctxOf π) f = ofGlobal (ctxOf π) (dict k)) (π : ι → Rk α) {x y : α}
    (hxy : x ≠ y) : f ((x, y), col π x y) = (π k).1 x y := by
  have hv : ((x, y), col π x y) ∈ ctxOf π := (mem_ctxOf_iff π _).mpr ⟨hxy, rfl⟩
  have := congrFun (hk π) ((x, y), col π x y)
  simp only [ofGlobal, hv, ↓reduceIte, Option.some.injEq] at this
  exact this

/-- **Level 3.** With at least three alternatives and two voters, Arrow's
    scenario has global sections, the dictatorships, and none is fixed by the
    permutations of the voters. -/
theorem level3 (hα : 3 ≤ Fintype.card α) (hι : 2 ≤ Fintype.card ι) :
    Level3 (voters (ι := ι) (α := α)) := by
  obtain ⟨k₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  refine ⟨⟨dict k₀, dict_global k₀⟩, ?_⟩
  rintro ⟨f, hf, hsym⟩
  obtain ⟨k, hk⟩ := global_dict hα hf
  obtain ⟨j, hjk⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card ι) k
  obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card α)
  obtain ⟨σ, hσ⟩ := ArrowGeneral.exists_rk_above hxy
  -- voter k ranks x above y, all others the reverse
  let π : ι → Rk α := fun i => if i = k then σ else ArrowGeneral.revRk σ
  let g : Equiv.Perm ι := Equiv.swap k j
  have e1 := bit_of_dict hk π hxy
  have e2 := bit_of_dict hk (actP g⁻¹ π) hxy
  have e3 : f ((x, y), col (actP g⁻¹ π) x y) = f ((x, y), col π x y) := by
    have := congrFun (hsym g) ((x, y), col π x y)
    simp only [voters, onAf] at this
    refine Eq.trans ?_ this
    rfl
  have h := e1.symm.trans (e3.symm.trans e2)
  have hg : g⁻¹⁻¹ k = j := by rw [inv_inv]; exact Equiv.swap_apply_left k j
  have hπj : actP g⁻¹ π k = ArrowGeneral.revRk σ := by
    show π (g⁻¹⁻¹ k) = _
    rw [hg]
    simp [π, hjk]
  have hπk : π k = σ := by simp [π]
  rw [hπj, hπk, hσ] at h
  have hr : (ArrowGeneral.revRk σ).1 x y = false := PathPinning.asymm σ hσ
  rw [hr] at h
  exact Bool.noConfusion h

/-- Division (Proposition 1 of *Four Levels*) for Arrow's scenario: averaging
    a dictatorship over the voters' permutations gives a symmetric,
    non-contextual empirical model, random dictatorship, and no symmetric
    global section explains it. -/
theorem division_voters (hα : 3 ≤ Fintype.card α) (hι : 2 ≤ Fintype.card ι) :
    (∃ e, Scenarios.Model scen e ∧ NonContextual scen e ∧ SymModel (voters (ι := ι) (α := α)) e) ∧
      ¬ ∃ f, IsSymGlobal (voters (ι := ι) (α := α)) f :=
  division_of_level3 _ (level3 hα hι)

end ArrowScenario

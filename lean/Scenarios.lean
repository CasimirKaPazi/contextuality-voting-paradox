module

public import Mathlib

@[expose] public section

/-!
# Scenarios, empirical models and the four levels

*Four Levels of Obstruction in Social Choice*, Section 2, with Proposition 1 (division).

* Variables `V` and values `O`, both finite. A *local assignment* is a map `V → Option O`; the
  restriction of a global assignment `f : V → O` to a set `c` of variables is `ofGlobal c f`,
  which is `none` outside `c`. This avoids subtypes: a local assignment on `c` is a map that is
  `none` outside `c`.
* A scenario: a finite set of contexts (sets of variables) and, for each context, a predicate of
  admissibility on local assignments. Boundary conditions are part of admissibility.
* A *global section*: a global assignment admissible in every context.
* An *empirical model*: a distribution `e c` on local assignments for each context, supported on
  admissible assignments on `c`, with *full compatibility*: two contexts give the same marginal on
  their intersection. *Weak compatibility* asks this only for single shared variables
  (`Model.weak`).
* *Non-contextual*: the image of one distribution on global sections (`mix`).
* A *symmetry*: a group acting on contexts, global assignments and local assignments, compatible
  with restriction and admissibility. *Levels* 1–4 as in the draft.

`mix_model`: every distribution on global sections gives an empirical model.
`division`: averaging a global section over a finite symmetry group gives a symmetric,
non-contextual empirical model; at level 3 there is no symmetric global section to explain it.
-/

open Finset

namespace Scenarios

/-- Local assignments: `none` marks a variable outside the context. -/
abbrev Loc (V O : Type*) := V → Option O

variable {V O : Type*} [Fintype V] [DecidableEq V] [Fintype O] [DecidableEq O]

/-- Restriction of a local assignment to a set of variables. -/
def restr (T : Finset V) (ρ : Loc V O) : Loc V O := fun v => if v ∈ T then ρ v else none

/-- Restriction of a global assignment to a set of variables. -/
def ofGlobal (T : Finset V) (f : V → O) : Loc V O := fun v => if v ∈ T then some (f v) else none

omit [Fintype V] [Fintype O] [DecidableEq O] in
lemma restr_ofGlobal (T c : Finset V) (f : V → O) :
    restr T (ofGlobal c f) = ofGlobal (T ∩ c) f := by
  funext v
  simp only [restr, ofGlobal, mem_inter]
  by_cases hT : v ∈ T <;> by_cases hc : v ∈ c <;> simp [hT, hc]

omit [Fintype V] [Fintype O] [DecidableEq O] in
lemma restr_restr {T T' : Finset V} (h : T ⊆ T') (ρ : Loc V O) :
    restr T (restr T' ρ) = restr T ρ := by
  funext v
  simp only [restr]
  by_cases hv : v ∈ T
  · simp [hv, h hv]
  · simp [hv]

/-- A scenario: contexts and admissible local assignments. -/
structure Scenario (V O : Type*) where
  ctx : Finset (Finset V)
  adm : Finset V → Loc V O → Prop

variable (S : Scenario V O)

/-- A global section. -/
def IsGlobal (f : V → O) : Prop := ∀ c ∈ S.ctx, S.adm c (ofGlobal c f)

/-- Marginal of a distribution on local assignments on a set `T` of variables. -/
def marg (μ : Loc V O → ℝ) (T : Finset V) (τ : Loc V O) : ℝ :=
  ∑ ρ ∈ univ.filter (fun ρ => restr T ρ = τ), μ ρ

/-- Empirical model with full compatibility. -/
structure Model (e : Finset V → Loc V O → ℝ) : Prop where
  nonneg : ∀ c ρ, 0 ≤ e c ρ
  total : ∀ c ∈ S.ctx, ∑ ρ, e c ρ = 1
  supp : ∀ c ∈ S.ctx, ∀ ρ, e c ρ ≠ 0 → S.adm c ρ ∧ ∃ f, ρ = ofGlobal c f
  compat : ∀ c ∈ S.ctx, ∀ c' ∈ S.ctx, ∀ τ, marg (e c) (c ∩ c') τ = marg (e c') (c ∩ c') τ

/-- Empirical model with weak compatibility: agreement on single shared variables. -/
structure WeakModel (e : Finset V → Loc V O → ℝ) : Prop where
  nonneg : ∀ c ρ, 0 ≤ e c ρ
  total : ∀ c ∈ S.ctx, ∑ ρ, e c ρ = 1
  supp : ∀ c ∈ S.ctx, ∀ ρ, e c ρ ≠ 0 → S.adm c ρ ∧ ∃ f, ρ = ofGlobal c f
  compat : ∀ c ∈ S.ctx, ∀ c' ∈ S.ctx, ∀ v ∈ c ∩ c', ∀ τ,
    marg (e c) {v} τ = marg (e c') {v} τ

/-- The model induced by a distribution `d` on global assignments. -/
def mix (d : (V → O) → ℝ) (c : Finset V) (ρ : Loc V O) : ℝ :=
  ∑ f ∈ univ.filter (fun f => ofGlobal c f = ρ), d f

/-- Non-contextual: induced by a distribution on global sections. -/
def NonContextual (e : Finset V → Loc V O → ℝ) : Prop :=
  ∃ d : (V → O) → ℝ, (∀ f, 0 ≤ d f) ∧ ∑ f, d f = 1 ∧ (∀ f, d f ≠ 0 → IsGlobal S f) ∧
    ∀ c ∈ S.ctx, ∀ ρ, e c ρ = mix d c ρ

/-! ### Marginals -/

lemma marg_of_sub (μ : Loc V O → ℝ) {T T' : Finset V} (h : T ⊆ T') (τ : Loc V O) :
    marg μ T τ = ∑ τ' ∈ univ.filter (fun τ' => restr T τ' = τ), marg μ T' τ' := by
  unfold marg
  rw [sum_comm' (t' := univ.filter (fun ρ => restr T (restr T' ρ) = τ))
    (s' := fun ρ => {restr T' ρ})]
  · simp only [sum_singleton, restr_restr h]
  · intro τ' ρ
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨h1, rfl⟩; exact ⟨rfl, h1⟩
    · rintro ⟨rfl, h2⟩; exact ⟨h2, rfl⟩

/-- Full compatibility implies weak compatibility. -/
theorem Model.weak {e : Finset V → Loc V O → ℝ} (h : Model S e) : WeakModel S e where
  nonneg := h.nonneg
  total := h.total
  supp := h.supp
  compat := by
    intro c hc c' hc' v hv τ
    have hsub : ({v} : Finset V) ⊆ c ∩ c' := singleton_subset_iff.mpr hv
    rw [marg_of_sub _ hsub, marg_of_sub _ hsub]
    exact sum_congr rfl (fun τ' _ => h.compat c hc c' hc' τ')

lemma marg_mix (d : (V → O) → ℝ) (c T : Finset V) (τ : Loc V O) :
    marg (mix d c) T τ = ∑ f ∈ univ.filter (fun f => ofGlobal (T ∩ c) f = τ), d f := by
  unfold marg mix
  rw [sum_comm' (t' := univ.filter (fun f => restr T (ofGlobal c f) = τ))
    (s' := fun f => {ofGlobal c f})]
  · simp only [sum_singleton, restr_ofGlobal]
  · intro ρ f
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨h1, rfl⟩; exact ⟨rfl, h1⟩
    · rintro ⟨rfl, h2⟩; exact ⟨h2, rfl⟩

/-- Every distribution on global sections induces an empirical model. -/
theorem mix_model {d : (V → O) → ℝ} (h0 : ∀ f, 0 ≤ d f) (h1 : ∑ f, d f = 1)
    (hg : ∀ f, d f ≠ 0 → IsGlobal S f) : Model S (mix d) where
  nonneg := fun c ρ => sum_nonneg (fun f _ => h0 f)
  total := by
    intro c _
    unfold mix
    simp only [sum_filter]
    rw [sum_comm]
    simp [h1]
  supp := by
    intro c hc ρ hρ
    unfold mix at hρ
    obtain ⟨f, hf, hdf⟩ := exists_ne_zero_of_sum_ne_zero hρ
    simp only [mem_filter, mem_univ, true_and] at hf
    rw [← hf]
    exact ⟨hg f hdf c hc, f, rfl⟩
  compat := by
    intro c _ c' _ τ
    rw [marg_mix, marg_mix]
    have e1 : c ∩ c' ∩ c = c ∩ c' := by ext v; simp only [mem_inter]; tauto
    have e2 : c ∩ c' ∩ c' = c ∩ c' := by ext v; simp only [mem_inter]; tauto
    rw [e1, e2]

theorem mix_nonContextual {d : (V → O) → ℝ} (h0 : ∀ f, 0 ≤ d f) (h1 : ∑ f, d f = 1)
    (hg : ∀ f, d f ≠ 0 → IsGlobal S f) : NonContextual S (mix d) :=
  ⟨d, h0, h1, hg, fun _ _ _ => rfl⟩

/-! ### Symmetry and levels -/

/-- A group acting on contexts, global and local assignments, compatibly with restriction and
admissibility. -/
structure Symmetry (G : Type*) [Group G] where
  onC : G → Finset V → Finset V
  onA : G → (V → O) → (V → O)
  onL : G → Loc V O → Loc V O
  onC_mul : ∀ g h c, onC (g * h) c = onC g (onC h c)
  onC_one : ∀ c, onC 1 c = c
  onA_mul : ∀ g h f, onA (g * h) f = onA g (onA h f)
  onL_inj : ∀ g, Function.Injective (onL g)
  ctx_mem : ∀ g c, c ∈ S.ctx → onC g c ∈ S.ctx
  adm_iff : ∀ g c ρ, S.adm (onC g c) (onL g ρ) ↔ S.adm c ρ
  res : ∀ g c f, ofGlobal (onC g c) (onA g f) = onL g (ofGlobal c f)

variable {S} {G : Type*} [Group G]

/-- A symmetric family of context distributions. -/
def SymModel (Y : Symmetry S G) (e : Finset V → Loc V O → ℝ) : Prop :=
  ∀ g, ∀ c ∈ S.ctx, ∀ ρ, e (Y.onC g c) (Y.onL g ρ) = e c ρ

/-- A symmetric global section. -/
def IsSymGlobal (Y : Symmetry S G) (f : V → O) : Prop := IsGlobal S f ∧ ∀ g, Y.onA g f = f

variable (S) in
def Level1 : Prop := ¬ ∃ e, Model S e
variable (S) in
def Level2 : Prop := (∃ e, Model S e) ∧ ¬ ∃ f, IsGlobal S f
def Level3 (Y : Symmetry S G) : Prop := (∃ f, IsGlobal S f) ∧ ¬ ∃ f, IsSymGlobal Y f
def Level4 (Y : Symmetry S G) : Prop := ∃ f, IsSymGlobal Y f

omit [Fintype V] [Fintype O] [DecidableEq O] in
lemma isGlobal_act (Y : Symmetry S G) {f : V → O} (hf : IsGlobal S f) (g : G) :
    IsGlobal S (Y.onA g f) := by
  intro c hc
  have hc0 : Y.onC g (Y.onC g⁻¹ c) = c := by rw [← Y.onC_mul, mul_inv_cancel, Y.onC_one]
  rw [← hc0, Y.res, Y.adm_iff]
  exact hf _ (Y.ctx_mem _ _ hc)

/-- The uniform average of the images of `s` under the group. -/
noncomputable def avg (Y : Symmetry S G) [Fintype G] (s : V → O) (f : V → O) : ℝ :=
  ∑ g : G, if Y.onA g s = f then (Fintype.card G : ℝ)⁻¹ else 0

omit [Group G] in
lemma mix_avg [Fintype G] (a : G → (V → O)) (k : ℝ) (c : Finset V) (ρ : Loc V O) :
    mix (fun f => ∑ g, if a g = f then k else 0) c ρ =
      ∑ g, if ofGlobal c (a g) = ρ then k else 0 := by
  simp only [mix]
  rw [sum_comm]
  refine sum_congr rfl (fun g _ => ?_)
  rw [sum_ite_eq]
  simp [mem_filter]

/-- Proposition 1 of *Four Levels* (division): the average of a global section over a finite
symmetry group is a symmetric, non-contextual empirical model. -/
theorem division (Y : Symmetry S G) [Fintype G] {s : V → O} (hs : IsGlobal S s) :
    Model S (mix (avg Y s)) ∧ NonContextual S (mix (avg Y s)) ∧ SymModel Y (mix (avg Y s)) := by
  have hk : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h0 : ∀ f, 0 ≤ avg Y s f := fun f =>
    sum_nonneg (fun g _ => by split_ifs <;> positivity)
  have h1 : ∑ f, avg Y s f = 1 := by
    unfold avg
    rw [sum_comm]
    simp [hk]
  have hg : ∀ f, avg Y s f ≠ 0 → IsGlobal S f := by
    intro f hf
    unfold avg at hf
    obtain ⟨g, -, hgf⟩ := exists_ne_zero_of_sum_ne_zero hf
    by_cases h : Y.onA g s = f
    · rw [← h]; exact isGlobal_act Y hs g
    · simp [h] at hgf
  refine ⟨mix_model S h0 h1 hg, mix_nonContextual S h0 h1 hg, ?_⟩
  intro g c _ ρ
  unfold avg
  rw [mix_avg, mix_avg, ← Equiv.sum_comp (Equiv.mulLeft g)]
  refine sum_congr rfl (fun h _ => ?_)
  simp only [Equiv.coe_mulLeft, Y.onA_mul, Y.res, (Y.onL_inj g).eq_iff]

/-- At level 3, the averaged model is symmetric and non-contextual, while no symmetric global
section exists: among symmetric objects the scenario is at level 2. -/
theorem division_of_level3 (Y : Symmetry S G) [Fintype G] (h : Level3 Y) :
    (∃ e, Model S e ∧ NonContextual S e ∧ SymModel Y e) ∧ ¬ ∃ f, IsSymGlobal Y f := by
  obtain ⟨⟨s, hs⟩, hno⟩ := h
  exact ⟨⟨_, division Y hs⟩, hno⟩

end Scenarios

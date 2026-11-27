/-
  The bridge between the two encodings of the Gibbard–Satterthwaite scenario
  for three alternatives: the hexagon of `GlobalFormLottery.lean` and
  `ContextualFraction.lean` (rankings as `Fin 6`), and the general frame of
  `GSScenario.lean` (rankings as `PathPinning.Rk (Fin 3)`, profiles as
  variables of a `Scenarios.Scenario`).

  * `hexRk`: the six hexagon rankings as rankings of `Fin 3`; a bijection
    (`hexRk_bij`), whose upper sets are ∅, the top, the top two and everything
    (`upR_hex`). `profE` carries it to profiles, `hexL` to rules.
  * `sdspR_iff`, `sdspRule_iff`, `model_iff`: SD-SP in the two encodings
    agree for lotteries, so `ContextualFraction.Model` is the existence of an
    empirical model of the scenario with those marginals (via `gs_prop1`).
  * `detSP_iff_global`: the deterministic SP rules of `ContextualFraction`
    are the global sections of the scenario (`isGlobal_iff`: a global
    assignment is a global section exactly when no voter gains by switching
    ballots, in either direction).
  * `nc_iff_scenario`: a lottery rule is non-contextual in the sense of
    `ContextualFraction` (a mixture of deterministic SP rules) exactly when
    some empirical model with these marginals is non-contextual in the sense
    of `Scenarios`. The empirical model is not determined by its marginals:
    contexts are pairs of profiles, and a joint draw on a pair carries more
    than its two marginals. So the statement is about the existence of such
    a model.
  * `nc_iff_deg_scenario`: Proposition 5's criterion in the language of the
    scenario: an SD-SP lottery rule admits a non-contextual empirical model
    exactly when no degree is negative (with Gibbard's theorem as in
    `ContextualFraction`).

  Not bridged: the contextual fraction. `ContextualFraction.cf` is the least
  weight over decompositions of the marginals; for one given empirical model,
  whose joint draws on pairs are fixed, the least weight can be larger.
-/

module

public import Mathlib
public import ContextualFraction
public import GSScenario

@[expose] public section

open Finset Scenarios GlobalFormLottery

namespace ContextualBridge

/-! ### The six rankings -/

/-- The position of x in the hexagon ranking r: 0 for the top, 1 for the
    second, 2 for the bottom. -/
def posFn (r : Fin 6) (x : Fin 3) : ℕ := if x = top r then 0 else if x = sec r then 1 else 2

lemma posFn_inj : ∀ r, Function.Injective (posFn r) := by decide

/-- The hexagon ranking r as a ranking of `Fin 3`. -/
def hexRk (r : Fin 6) : PathPinning.Rk (Fin 3) := Rankings.toRk (posFn r) (posFn_inj r)

lemma hexRk_inj : Function.Injective hexRk := by decide +kernel

lemma hexRk_surj : Function.Surjective hexRk := by decide +kernel

lemma hexRk_bij : Function.Bijective hexRk := ⟨hexRk_inj, hexRk_surj⟩

/-- The hexagon rankings are all rankings of three alternatives. -/
noncomputable def hexEquiv : Fin 6 ≃ PathPinning.Rk (Fin 3) := Equiv.ofBijective hexRk hexRk_bij

lemma top_ne_sec : ∀ r : Fin 6, top r ≠ sec r := by decide

instance (ρ : PathPinning.Rk (Fin 3)) (U : Finset (Fin 3)) : Decidable (Rankings.UpR ρ U) := by
  unfold Rankings.UpR; infer_instance

/-- The upper sets of a hexagon ranking. -/
lemma upR_hex : ∀ (r : Fin 6) (U : Finset (Fin 3)), Rankings.UpR (hexRk r) U ↔
    (U = ∅ ∨ U = {top r} ∨ U = {top r, sec r} ∨ U = univ) := by decide +kernel

/-- SD-SP for one voter in the two encodings, for lotteries. -/
lemma sdspR_iff (L : PathPinning.Rk (Fin 3) → Fin 3 → ℝ) (h1 : ∀ ρ, ∑ a, L ρ a = 1) :
    Rankings.SDSPR L ↔ SDSP (fun r => L (hexRk r)) := by
  constructor
  · intro h r r'
    have hs := h (hexRk r) (hexRk r') {top r} ((upR_hex r _).mpr (Or.inr (Or.inl rfl)))
    have hp := h (hexRk r) (hexRk r') {top r, sec r} ((upR_hex r _).mpr (Or.inr (Or.inr (Or.inl rfl))))
    rw [sum_singleton, sum_singleton] at hs
    rw [sum_pair (top_ne_sec r), sum_pair (top_ne_sec r)] at hp
    exact ⟨hs, hp⟩
  · intro h ρ τ U hU
    obtain ⟨r, rfl⟩ := hexRk_surj ρ
    obtain ⟨r', rfl⟩ := hexRk_surj τ
    rcases (upR_hex r U).mp hU with rfl | rfl | rfl | rfl
    · simp
    · rw [sum_singleton, sum_singleton]
      exact (h r r').1
    · rw [sum_pair (top_ne_sec r), sum_pair (top_ne_sec r)]
      exact (h r r').2
    · rw [h1, h1]

/-- For point masses: SD-SP of a deterministic one-voter rule says that the
    outcome under the true ranking is at least as good as under any other. -/
lemma pt_pair (r : Fin 6) (a b : Fin 3) :
    (pt b (top r) ≤ pt a (top r) ∧ pt b (top r) + pt b (sec r) ≤ pt a (top r) + pt a (sec r)) ↔
      (a = b ∨ (hexRk r).1 a b = true) := by
  fin_cases r <;> fin_cases a <;> fin_cases b <;>
    norm_num [pt, top, sec, hexRk, Rankings.toRk, posFn]

lemma pt_sdsp_iff (g : Fin 6 → Fin 3) :
    SDSP (fun r => pt (g r)) ↔ ∀ r r', g r = g r' ∨ (hexRk r).1 (g r) (g r') = true :=
  forall_congr' fun r => forall_congr' fun r' => pt_pair r (g r) (g r')

/-! ### Profiles and rules -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Hexagon profiles as profiles of the scenario. -/
noncomputable def profE : ContextualFraction.Prof ι ≃ GSScenario.Prof ι (Fin 3) :=
  Equiv.piCongrRight fun _ => hexEquiv

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma profE_apply (π : ContextualFraction.Prof ι) (i : ι) : profE π i = hexRk (π i) := rfl

omit [Fintype ι] in
lemma profE_update (π : ContextualFraction.Prof ι) (k : ι) (r : Fin 6) :
    profE (Function.update π k r) = Function.update (profE π) k (hexRk r) := by
  funext i
  by_cases hi : i = k
  · subst hi; simp
  · simp [Function.update_of_ne hi]

/-- A rule of the scenario read on hexagon profiles. -/
noncomputable def hexL (L : GSScenario.Prof ι (Fin 3) → Fin 3 → ℝ) : ContextualFraction.LRule ι :=
  fun π => L (profE π)

omit [Fintype ι] in
lemma slice_hexL (L : GSScenario.Prof ι (Fin 3) → Fin 3 → ℝ) (π : ContextualFraction.Prof ι)
    (k : ι) : ContextualFraction.slice (hexL L) π k =
      fun r => L (Function.update (profE π) k (hexRk r)) := by
  funext r
  simp only [ContextualFraction.slice, hexL, profE_update]

omit [Fintype ι] in
/-- SD-SP rules in the two encodings agree, for lotteries. -/
lemma sdspRule_iff (L : GSScenario.Prof ι (Fin 3) → Fin 3 → ℝ) (h1 : ∀ π, ∑ a, L π a = 1) :
    GSScenario.SDSPRule L ↔ ContextualFraction.SDSPn (hexL L) := by
  constructor
  · intro h π k
    rw [slice_hexL]
    exact (sdspR_iff _ fun ρ => h1 _).mp (h (profE π) k)
  · intro h P k
    obtain ⟨π, rfl⟩ := profE.surjective P
    have := h π k
    rw [slice_hexL] at this
    exact (sdspR_iff _ fun ρ => h1 _).mpr this

/-- The models of `ContextualFraction` are the lottery rules of the scenario
    that have an empirical model with these marginals. -/
theorem model_iff (L : GSScenario.Prof ι (Fin 3) → Fin 3 → ℝ) (h0 : ∀ π a, 0 ≤ L π a)
    (h1 : ∀ π, ∑ a, L π a = 1) :
    ContextualFraction.Model (hexL L) ↔
      ∃ e, Model GSScenario.GS e ∧ GSScenario.HasMarginals e L := by
  rw [GSScenario.gs_prop1 h0 h1, sdspRule_iff L h1]
  refine ⟨fun h => h.2, fun h => ⟨fun π => ⟨fun x => h0 _ x, ?_⟩, h⟩⟩
  have := h1 (profE π)
  rw [Fin.sum_univ_three] at this
  exact this

/-! ### Global sections are the deterministic SP rules -/

/-- A global assignment is a global section of the scenario exactly when no
    voter gains by switching ballots, in either direction. -/
lemma isGlobal_iff (F : GSScenario.Prof ι (Fin 3) → Fin 3) :
    IsGlobal GSScenario.GS F ↔ ∀ (P : GSScenario.Prof ι (Fin 3)) (k : ι)
      (σ τ : PathPinning.Rk (Fin 3)),
      Rankings.AdmR σ τ (F (Function.update P k σ)) (F (Function.update P k τ)) := by
  constructor
  · intro hF P k σ τ
    by_cases hst : σ = τ
    · subst hst
      exact ⟨Or.inl rfl, Or.inl rfl⟩
    · have hnb := GSScenario.nb_update P k hst
      have hc : ({Function.update P k σ, Function.update P k τ} :
          Finset (GSScenario.Prof ι (Fin 3))) ∈ (GSScenario.GS).ctx :=
        GSScenario.mem_ctxs.mpr ⟨_, _, k, hnb, rfl⟩
      have hm1 : Function.update P k σ ∈ ({Function.update P k σ, Function.update P k τ} :
          Finset (GSScenario.Prof ι (Fin 3))) := by simp
      have hm2 : Function.update P k τ ∈ ({Function.update P k σ, Function.update P k τ} :
          Finset (GSScenario.Prof ι (Fin 3))) := by simp
      have := hF _ hc _ hm1 _ hm2 k hnb _ _ (GSScenario.ofGlobal_mem hm1)
        (GSScenario.ofGlobal_mem hm2)
      simpa using this
  · intro h c hc Q hQ Q' hQ' k hk x x' hx hx'
    rw [GSScenario.ofGlobal_mem hQ] at hx
    rw [GSScenario.ofGlobal_mem hQ'] at hx'
    obtain rfl := Option.some_injective _ hx
    obtain rfl := Option.some_injective _ hx'
    have := h Q k (Q k) (Q' k)
    rwa [Function.update_eq_self, GSScenario.update_nb hk] at this

/-- The deterministic SP rules of `ContextualFraction` are the global sections. -/
theorem detSP_iff_global (F : GSScenario.Prof ι (Fin 3) → Fin 3) :
    ContextualFraction.DetSP (fun π => F (profE π)) ↔ IsGlobal GSScenario.GS F := by
  rw [isGlobal_iff]
  have hslice : ∀ π k, ContextualFraction.slice (fun π x => pt (F (profE π)) x) π k =
      fun r => pt (F (Function.update (profE π) k (hexRk r))) := fun π k => by
    funext r x
    simp only [ContextualFraction.slice, profE_update]
  unfold ContextualFraction.DetSP ContextualFraction.SDSPn
  simp only [hslice, pt_sdsp_iff]
  constructor
  · intro h P k σ τ
    obtain ⟨π, rfl⟩ := profE.surjective P
    obtain ⟨r, rfl⟩ := hexRk_surj σ
    obtain ⟨r', rfl⟩ := hexRk_surj τ
    exact ⟨h π k r r', h π k r' r⟩
  · intro h π k r r'
    exact (h (profE π) k (hexRk r) (hexRk r')).1

/-! ### Non-contextual rules and non-contextual models -/

omit [Fintype ι] in
lemma pt_eq_ite (y x : Fin 3) : pt y x = if y = x then 1 else 0 := by
  unfold pt
  by_cases h : y = x
  · rw [ite_eq_left h.symm, ite_eq_left h]
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]

/-- A cone of deterministic SP rules is a distribution on them. -/
lemma NCc.dist {N : ContextualFraction.LRule ι} {t : ℝ} (h : ContextualFraction.NCc N t) :
    ∃ d : (ContextualFraction.Prof ι → Fin 3) → ℝ, (∀ g, 0 ≤ d g) ∧ ∑ g, d g = t ∧
      (∀ g, d g ≠ 0 → ContextualFraction.DetSP g) ∧ ∀ π x, N π x = ∑ g, d g * pt (g π) x := by
  classical
  induction h with
  | zero => exact ⟨fun _ => 0, fun _ => le_refl _, by simp, fun _ h => absurd rfl h, by simp⟩
  | det g c hg hc =>
    refine ⟨fun g' => if g' = g then c else 0, fun g' => by by_cases e : g' = g <;> simp [e, hc],
      by simp, fun g' h => ?_, fun π x => ?_⟩
    · by_cases e : g' = g
      · rw [e]; exact hg
      · simp [e] at h
    · simp [ite_mul]
  | @add N M s t _ _ ih1 ih2 =>
    obtain ⟨d1, h10, h11, h1g, h1N⟩ := ih1
    obtain ⟨d2, h20, h21, h2g, h2N⟩ := ih2
    refine ⟨fun g => d1 g + d2 g, fun g => add_nonneg (h10 g) (h20 g),
      by rw [sum_add_distrib, h11, h21], fun g h => ?_, fun π x => ?_⟩
    · have h' : d1 g + d2 g ≠ 0 := h
      by_cases e : d1 g = 0
      · exact h2g g (by rw [e, zero_add] at h'; exact h')
      · exact h1g g e
    · show N π x + M π x = _
      rw [h1N, h2N, ← sum_add_distrib]
      exact sum_congr rfl fun g _ => by ring

/-- A distribution on deterministic SP rules is a cone. -/
lemma NCc.of_dist (d : (ContextualFraction.Prof ι → Fin 3) → ℝ) (h0 : ∀ g, 0 ≤ d g)
    (hg : ∀ g, d g ≠ 0 → ContextualFraction.DetSP g) :
    ContextualFraction.NCc (fun π x => ∑ g, d g * pt (g π) x) (∑ g, d g) := by
  classical
  have h := ContextualFraction.NCc.finsum (univ.filter fun g => d g ≠ 0)
    (N := fun g π x => d g * pt (g π) x) (t := d)
    (fun g hg' => ContextualFraction.NCc.det g (d g) (hg g (mem_filter.mp hg').2) (h0 g))
  refine h.congr (fun π x => ?_) ?_
  · show ∑ g ∈ univ.filter (fun g => d g ≠ 0), d g * pt (g π) x = ∑ g, d g * pt (g π) x
    refine sum_subset (filter_subset _ _) fun g _ hg' => ?_
    simp only [mem_filter, mem_univ, true_and, not_not] at hg'
    rw [hg', zero_mul]
  · exact sum_filter_ne_zero _

/-- The rules on hexagon profiles, as global assignments of the scenario. -/
noncomputable def ruleE : (GSScenario.Prof ι (Fin 3) → Fin 3) ≃ (ContextualFraction.Prof ι → Fin 3) :=
  (profE.arrowCongr (Equiv.refl (Fin 3))).symm

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma ruleE_apply (F : GSScenario.Prof ι (Fin 3) → Fin 3) (π : ContextualFraction.Prof ι) :
    ruleE F π = F (profE π) := by
  simp [ruleE, Equiv.arrowCongr]

/-- The one-profile marginal of a mixture of global assignments. -/
lemma marg_mix_single (D : (GSScenario.Prof ι (Fin 3) → Fin 3) → ℝ)
    {c : Finset (GSScenario.Prof ι (Fin 3))} {v : GSScenario.Prof ι (Fin 3)} (hv : v ∈ c)
    (x : Fin 3) :
    marg (Scenarios.mix D c) {v} (GSScenario.ptG v x) = ∑ F, D F * pt (F v) x := by
  rw [marg_mix, singleton_inter_of_mem hv]
  have : ∀ F : GSScenario.Prof ι (Fin 3) → Fin 3,
      ofGlobal {v} F = GSScenario.ptG v x ↔ F v = x := fun F => by
    constructor
    · intro hF
      have h' := congrFun hF v
      rw [GSScenario.ptG, GSScenario.ofGlobal_mem (mem_singleton_self v),
        GSScenario.ofGlobal_mem (mem_singleton_self v)] at h'
      exact Option.some_injective _ h'
    · intro hF
      exact GSScenario.ofGlobal_eq_of fun w hw => by rw [mem_singleton.mp hw, hF]
  rw [sum_filter]
  refine sum_congr rfl fun F _ => ?_
  by_cases hF : F v = x
  · rw [ite_eq_left ((this F).mpr hF), pt_eq_ite, ite_eq_left hF, mul_one]
  · rw [ite_eq_right (fun h => hF ((this F).mp h)), pt_eq_ite, ite_eq_right hF, mul_zero]

/-- Every profile lies in some context, when there is a voter. -/
lemma exists_ctx [Nonempty ι] (v : GSScenario.Prof ι (Fin 3)) :
    ∃ c ∈ (GSScenario.GS : Scenario (GSScenario.Prof ι (Fin 3)) (Fin 3)).ctx, v ∈ c := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨σ, hσ⟩ : ∃ σ : PathPinning.Rk (Fin 3), σ ≠ v i := by
    by_cases h : hexRk 0 = v i
    · exact ⟨hexRk 1, fun e => absurd (hexRk_inj (e.trans h.symm)) (by decide)⟩
    · exact ⟨hexRk 0, h⟩
  have hnb := GSScenario.nb_update v i (Ne.symm hσ)
  rw [Function.update_eq_self] at hnb
  exact ⟨{v, Function.update v i σ}, GSScenario.mem_ctxs.mpr ⟨_, _, i, hnb, rfl⟩,
    mem_insert_self _ _⟩

/-- **The bridge.** A lottery rule is non-contextual in the sense of
    `ContextualFraction` (a mixture of deterministic SP rules) exactly when
    some empirical model of the scenario with these marginals is
    non-contextual in the sense of `Scenarios`. -/
theorem nc_iff_scenario [Nonempty ι] (L : GSScenario.Prof ι (Fin 3) → Fin 3 → ℝ) :
    ContextualFraction.NC (hexL L) ↔
      ∃ e, Model GSScenario.GS e ∧ GSScenario.HasMarginals e L ∧
        NonContextual GSScenario.GS e := by
  constructor
  · intro h
    obtain ⟨d, hd0, hd1, hdg, hdN⟩ := NCc.dist h
    let D : (GSScenario.Prof ι (Fin 3) → Fin 3) → ℝ := fun F => d (ruleE F)
    have hD0 : ∀ F, 0 ≤ D F := fun F => hd0 _
    have hD1 : ∑ F, D F = 1 := by rw [← hd1]; exact Equiv.sum_comp ruleE d
    have hDg : ∀ F, D F ≠ 0 → IsGlobal GSScenario.GS F := fun F hF => by
      have := hdg _ hF
      rw [show ruleE F = fun π => F (profE π) from funext (ruleE_apply F)] at this
      exact (detSP_iff_global F).mp this
    refine ⟨Scenarios.mix D, mix_model _ hD0 hD1 hDg, fun c _ v hv x => ?_,
      ⟨D, hD0, hD1, hDg, fun _ _ _ => rfl⟩⟩
    rw [marg_mix_single D hv]
    obtain ⟨π, rfl⟩ := profE.surjective v
    have := hdN π x
    simp only [hexL] at this
    rw [this, ← Equiv.sum_comp ruleE]
    exact sum_congr rfl fun F _ => by simp only [D, ruleE_apply]
  · rintro ⟨e, -, hm, d, hd0, hd1, hdg, hde⟩
    have hL : ∀ v x, L v x = ∑ F, d F * pt (F v) x := fun v x => by
      obtain ⟨c, hc, hv⟩ := exists_ctx v
      rw [← hm c hc v hv x, funext (hde c hc), marg_mix_single d hv]
    let d' : (ContextualFraction.Prof ι → Fin 3) → ℝ := fun g => d (ruleE.symm g)
    have h' := NCc.of_dist d' (fun g => hd0 _) fun g hg => by
      have := hdg _ hg
      rw [← detSP_iff_global] at this
      have he : (fun π => ruleE.symm g (profE π)) = g := by
        funext π
        rw [← ruleE_apply (ruleE.symm g) π, Equiv.apply_symm_apply]
      rwa [he] at this
    refine h'.congr (fun π x => ?_) ?_
    · simp only [hexL, hL, d']
      rw [← Equiv.sum_comp ruleE.symm]
      refine sum_congr rfl fun g _ => ?_
      rw [show ruleE.symm g (profE π) = g π by rw [← ruleE_apply (ruleE.symm g) π, Equiv.apply_symm_apply]]
    · rw [← hd1]
      exact Equiv.sum_comp ruleE.symm d

/-- **Proposition 5 in the scenario.** Under Gibbard's theorem, an SD-SP
    lottery rule admits a non-contextual empirical model of the scenario
    exactly when no degree is negative. -/
theorem nc_iff_deg_scenario [Nonempty ι] (hG : ContextualFraction.Gibbard1977 ι)
    (L : GSScenario.Prof ι (Fin 3) → Fin 3 → ℝ) (h0 : ∀ π a, 0 ≤ L π a)
    (h1 : ∀ π, ∑ a, L π a = 1) (hS : GSScenario.SDSPRule L) :
    (∃ e, Model GSScenario.GS e ∧ GSScenario.HasMarginals e L ∧
        NonContextual GSScenario.GS e) ↔
      ∀ π i, 0 ≤ ContextualFraction.degAt (hexL L) π i := by
  have hM : ContextualFraction.Model (hexL L) :=
    (model_iff L h0 h1).mpr ((GSScenario.gs_prop1 h0 h1).mpr hS)
  rw [← nc_iff_scenario L, ContextualFraction.nc_iff hG hM]

end ContextualBridge

module

public import Mathlib
public import Scenarios
public import Rankings

@[expose] public section

/-!
# The Gibbard–Satterthwaite scenario

*Gibbard–Satterthwaite as a Scenario*, Section 1 and Proposition 1, as an instance of the general
frame of `Scenarios.lean`.

* Variables: the profiles `π : ι → Rk α`; values: the alternatives `α`.
* Contexts: the pairs `{π, π'}` of profiles that differ in exactly one voter's ballot (`Nb`).
* Admissible: for both orders of the pair, the switching voter gains in neither direction
  (`Rankings.AdmR`). No boundary condition (unanimity is left out).

`gs_prop1`: a family of lotteries `L π` (nonnegative, summing to 1) is the family of one-profile
marginals of an empirical model with full compatibility exactly when it is SD-strategy-proof for
every voter at every profile of the others. Contexts meet in at most one variable, so full
compatibility comes down to the one-profile marginals (`compat_of_pairs`); the joint draws come
from `Rankings.prop1R`.
-/

open Finset Scenarios

namespace GSScenario

/-! ### Contexts that are pairs -/

section Pairs

variable {V O : Type*} [Fintype V] [DecidableEq V] [Fintype O] [DecidableEq O]

/-- The local assignment with value `x` at `v` only. -/
def ptG (v : V) (x : O) : Loc V O := ofGlobal {v} (fun _ => x)

/-- The global assignment with value `x` at `p` and `y` elsewhere. -/
def two (p : V) (x y : O) : V → O := fun v => if v = p then x else y

omit [Fintype V] [Fintype O] [DecidableEq O] in
lemma ofGlobal_eq_of {T : Finset V} {f g : V → O} (h : ∀ v ∈ T, f v = g v) :
    ofGlobal T f = ofGlobal T g := by
  funext v
  unfold ofGlobal
  by_cases hv : v ∈ T
  · simp [hv, h v hv]
  · simp [hv]

omit [Fintype V] [Fintype O] [DecidableEq O] in
lemma ofGlobal_mem {T : Finset V} {f : V → O} {v : V} (hv : v ∈ T) :
    ofGlobal T f v = some (f v) := by
  simp [ofGlobal, hv]

omit [Fintype V] [Fintype O] [DecidableEq O] in
lemma ptG_inj {v : V} {x y : O} (h : ptG v x = ptG v y) : x = y := by
  have h' := congrFun h v
  rw [ptG, ptG, ofGlobal_mem (mem_singleton_self v), ofGlobal_mem (mem_singleton_self v)] at h'
  exact Option.some_injective _ h'

omit [Fintype V] [Fintype O] [DecidableEq O] in
lemma restr_single_ofGlobal {c : Finset V} {v : V} (hv : v ∈ c) (f : V → O) :
    restr {v} (ofGlobal c f) = ptG v (f v) := by
  rw [restr_ofGlobal, singleton_inter_of_mem hv]
  exact ofGlobal_eq_of (fun w hw => by rw [mem_singleton] at hw; rw [hw])

omit [Fintype V] [Fintype O] [DecidableEq O] in
lemma restr_empty (ρ : Loc V O) : restr ∅ ρ = fun _ => none := by
  funext v
  simp [restr]

omit [Fintype V] [Fintype O] [DecidableEq O] in
lemma two_pair {p q : V} (hpq : p ≠ q) (f : V → O) :
    ofGlobal {p, q} f = ofGlobal {p, q} (two p (f p) (f q)) := by
  apply ofGlobal_eq_of
  intro v hv
  rcases mem_insert.mp hv with h | h
  · rw [h]; simp [two]
  · rw [mem_singleton.mp h]; simp [two, Ne.symm hpq]

omit [Fintype V] [Fintype O] [DecidableEq O] in
lemma two_swap {p q : V} (hpq : p ≠ q) (x y : O) :
    ofGlobal {p, q} (two q y x) = ofGlobal {p, q} (two p x y) := by
  apply ofGlobal_eq_of
  intro v hv
  rcases mem_insert.mp hv with h | h
  · rw [h]; simp [two, hpq]
  · rw [mem_singleton.mp h]; simp [two, Ne.symm hpq]

omit [Fintype V] [Fintype O] [DecidableEq O] in
lemma two_iff {p q : V} (hpq : p ≠ q) {x y x' y' : O} :
    ofGlobal {p, q} (two p x y) = ofGlobal {p, q} (two p x' y') ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    have h1 := congrFun h p
    have h2 := congrFun h q
    rw [ofGlobal_mem (mem_insert_self p {q}), ofGlobal_mem (mem_insert_self p {q})] at h1
    rw [ofGlobal_mem (mem_insert_of_mem (mem_singleton_self q)),
      ofGlobal_mem (mem_insert_of_mem (mem_singleton_self q))] at h2
    simp [two] at h1
    simp [two, Ne.symm hpq] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- The marginal at `p` of a distribution on a pair context, as a sum over the other value. -/
lemma marg_pt {μ : Loc V O → ℝ} {p q : V} (hpq : p ≠ q)
    (hs : ∀ ρ, μ ρ ≠ 0 → ∃ f, ρ = ofGlobal {p, q} f) (x : O) :
    marg μ {p} (ptG p x) = ∑ y, μ (ofGlobal {p, q} (two p x y)) := by
  have hinj : ∀ y ∈ (univ : Finset O), ∀ y' ∈ (univ : Finset O),
      ofGlobal {p, q} (two p x y) = ofGlobal {p, q} (two p x y') → y = y' :=
    fun y _ y' _ h => ((two_iff hpq).mp h).2
  rw [← sum_image hinj]
  unfold marg
  symm
  apply sum_subset
  · intro ρ hρ
    obtain ⟨y, -, rfl⟩ := mem_image.mp hρ
    simp only [mem_filter, mem_univ, true_and]
    rw [restr_single_ofGlobal (mem_insert_self p {q})]
    simp [two]
  · intro ρ hF hn
    by_contra hne
    obtain ⟨f, rfl⟩ := hs ρ hne
    simp only [mem_filter, mem_univ, true_and] at hF
    rw [restr_single_ofGlobal (mem_insert_self p {q})] at hF
    have hfp : f p = x := ptG_inj hF
    apply hn
    refine mem_image.mpr ⟨f q, mem_univ _, ?_⟩
    rw [two_pair hpq f, hfp]

/-- The marginal at a variable of the context, through the values there. -/
lemma marg_single {μ : Loc V O → ℝ} {c : Finset V}
    (hs : ∀ ρ, μ ρ ≠ 0 → ∃ f, ρ = ofGlobal c f) {v : V} (hv : v ∈ c) (τ : Loc V O) :
    marg μ {v} τ = ∑ x, if τ = ptG v x then marg μ {v} (ptG v x) else 0 := by
  by_cases h : ∃ x, τ = ptG v x
  · obtain ⟨x, rfl⟩ := h
    have h0 : ∀ y, y ≠ x →
        (if ptG v x = ptG v y then marg μ {v} (ptG v y) else 0) = 0 :=
      fun y hy => ite_eq_right (fun e => hy (ptG_inj e).symm)
    rw [Fintype.sum_eq_single x h0]
    simp
  · push Not at h
    rw [sum_eq_zero (fun x _ => ite_eq_right (h x))]
    unfold marg
    apply sum_eq_zero
    intro ρ hρ
    simp only [mem_filter, mem_univ, true_and] at hρ
    by_contra hne
    obtain ⟨f, rfl⟩ := hs ρ hne
    rw [restr_single_ofGlobal hv] at hρ
    exact h (f v) hρ.symm

/-- The marginal on no variables. -/
lemma marg_empty (μ : Loc V O → ℝ) (τ : Loc V O) :
    marg μ ∅ τ = if τ = (fun _ => none) then ∑ ρ, μ ρ else 0 := by
  unfold marg
  rw [sum_filter]
  by_cases h : τ = (fun _ => none)
  · rw [ite_eq_left h]
    refine sum_congr rfl (fun ρ _ => ?_)
    rw [ite_eq_left (show restr ∅ ρ = τ by rw [restr_empty, h])]
  · rw [ite_eq_right h]
    exact sum_eq_zero (fun ρ _ =>
      ite_eq_right (show ¬ restr ∅ ρ = τ by rw [restr_empty]; exact fun e => h e.symm))

omit [Fintype V] [Fintype O] [DecidableEq O] in
lemma card_inter_le_one {c c' : Finset V} (h2 : c.card = 2) (h2' : c'.card = 2) (hne : c ≠ c') :
    (c ∩ c').card ≤ 1 := by
  by_contra h
  push Not at h
  have e1 : c ∩ c' = c := eq_of_subset_of_card_le inter_subset_left (by omega)
  have e2 : c ∩ c' = c' := eq_of_subset_of_card_le inter_subset_right (by omega)
  exact hne (e1.symm.trans e2)

/-- When contexts are pairs, full compatibility comes down to the one-variable marginals. -/
theorem compat_of_pairs (S : Scenario V O) {e : Finset V → Loc V O → ℝ}
    (hpair : ∀ c ∈ S.ctx, c.card = 2) (htot : ∀ c ∈ S.ctx, ∑ ρ, e c ρ = 1)
    (hs : ∀ c ∈ S.ctx, ∀ ρ, e c ρ ≠ 0 → ∃ f, ρ = ofGlobal c f) (m : V → O → ℝ)
    (hm : ∀ c ∈ S.ctx, ∀ v ∈ c, ∀ x, marg (e c) {v} (ptG v x) = m v x) :
    ∀ c ∈ S.ctx, ∀ c' ∈ S.ctx, ∀ τ, marg (e c) (c ∩ c') τ = marg (e c') (c ∩ c') τ := by
  intro c hc c' hc' τ
  by_cases hcc : c = c'
  · rw [hcc]
  have hle := card_inter_le_one (hpair c hc) (hpair c' hc') hcc
  rcases Nat.lt_or_ge (c ∩ c').card 1 with h0 | h1
  · have hE : c ∩ c' = ∅ := card_eq_zero.mp (by omega)
    rw [hE, marg_empty, marg_empty, htot c hc, htot c' hc']
  · obtain ⟨v, hv⟩ := card_eq_one.mp (show (c ∩ c').card = 1 by omega)
    have hvi : v ∈ c ∩ c' := by rw [hv]; exact mem_singleton_self v
    have hvc : v ∈ c := mem_of_mem_inter_left hvi
    have hvc' : v ∈ c' := mem_of_mem_inter_right hvi
    rw [hv, marg_single (hs c hc) hvc, marg_single (hs c' hc') hvc']
    refine sum_congr rfl (fun x _ => ?_)
    rw [hm c hc v hvc, hm c' hc' v hvc']

end Pairs

/-! ### The scenario -/

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- Profiles. -/
abbrev Prof (ι α : Type*) [Fintype α] [DecidableEq α] := ι → PathPinning.Rk α

/-- `π` and `π'` differ, and only in the ballot of voter `k`. -/
def Nb (k : ι) (π π' : Prof ι α) : Prop := π ≠ π' ∧ ∀ j, j ≠ k → π j = π' j

open Classical in
/-- The contexts: pairs of profiles that differ in one voter's ballot. -/
noncomputable def ctxs : Finset (Finset (Prof ι α)) :=
  univ.filter (fun c => ∃ π π' k, Nb k π π' ∧ c = {π, π'})

/-- Admissible: for both orders of the pair, the switching voter gains in neither direction. -/
def admGS (c : Finset (Prof ι α)) (ρ : Loc (Prof ι α) α) : Prop :=
  ∀ π ∈ c, ∀ π' ∈ c, ∀ k, Nb k π π' → ∀ x x', ρ π = some x → ρ π' = some x' →
    Rankings.AdmR (π k) (π' k) x x'

/-- The Gibbard–Satterthwaite scenario (without boundary condition). -/
noncomputable def GS : Scenario (Prof ι α) α := ⟨ctxs, admGS⟩

/-- SD-strategy-proofness of a random rule: for every voter at every profile of the others. -/
def SDSPRule (L : Prof ι α → α → ℝ) : Prop :=
  ∀ (π : Prof ι α) (k : ι), Rankings.SDSPR (fun σ => L (Function.update π k σ))

/-- The one-profile marginals of `e` are the lotteries `L`. -/
def HasMarginals (e : Finset (Prof ι α) → Loc (Prof ι α) α → ℝ) (L : Prof ι α → α → ℝ) : Prop :=
  ∀ c ∈ (ctxs : Finset (Finset (Prof ι α))), ∀ v ∈ c, ∀ x, marg (e c) {v} (ptG v x) = L v x

lemma mem_ctxs {c : Finset (Prof ι α)} :
    c ∈ (ctxs : Finset (Finset (Prof ι α))) ↔ ∃ π π' k, Nb k π π' ∧ c = {π, π'} := by
  unfold ctxs
  simp only [mem_filter, mem_univ, true_and]

omit [Fintype ι] [DecidableEq ι] in
lemma nb_unique {k k' : ι} {π π' : Prof ι α} (h : Nb k π π')
    (h' : ∀ j, j ≠ k' → π j = π' j) : k' = k := by
  by_contra hkk
  apply h.1
  funext j
  by_cases hj : j = k
  · rw [hj]; exact h' k (Ne.symm hkk)
  · exact h.2 j hj

omit [Fintype ι] in
lemma update_nb {k : ι} {π π' : Prof ι α} (h : Nb k π π') : Function.update π k (π' k) = π' := by
  funext j
  by_cases hj : j = k
  · rw [hj]; simp
  · rw [Function.update_apply, ite_eq_right hj]; exact h.2 j hj

omit [Fintype ι] in
lemma nb_update (π : Prof ι α) (k : ι) {ρ τ : PathPinning.Rk α} (h : ρ ≠ τ) :
    Nb k (Function.update π k ρ) (Function.update π k τ) := by
  refine ⟨fun e => h ?_, fun j hj => ?_⟩
  · have := congrFun e k
    simpa using this
  · simp [hj]

lemma admR_swap {ρ τ : PathPinning.Rk α} {a b : α} (h : Rankings.AdmR ρ τ a b) :
    Rankings.AdmR τ ρ b a := ⟨h.2, h.1⟩

/-! ### From joint draws to an empirical model -/

/-- The context distribution built from a joint draw `J` of the lotteries at `π` and `π'`. -/
lemma local_props {L : Prof ι α → α → ℝ} (hL1 : ∀ π, ∑ x, L π x = 1)
    {π π' : Prof ι α} {k : ι} (hnb : Nb k π π') {J : α → α → ℝ}
    (hJ : (∀ a b, 0 ≤ J a b) ∧ (∀ a, ∑ b, J a b = L π a) ∧ (∀ b, ∑ a, J a b = L π' b) ∧
      (∀ a b, J a b ≠ 0 → Rankings.AdmR (π k) (π' k) a b))
    (c : Finset (Prof ι α)) (hcp : c = {π, π'}) (μ : Loc (Prof ι α) α → ℝ)
    (hμ : ∀ ρ, μ ρ = ∑ x, ∑ y, if ρ = ofGlobal c (two π x y) then J x y else 0) :
    (∀ ρ, 0 ≤ μ ρ) ∧ ∑ ρ, μ ρ = 1 ∧ (∀ ρ, μ ρ ≠ 0 → admGS c ρ ∧ ∃ f, ρ = ofGlobal c f) ∧
      (∀ x, marg μ {π} (ptG π x) = L π x) ∧ (∀ x, marg μ {π'} (ptG π' x) = L π' x) := by
  subst hcp
  obtain ⟨h0, hr, hc, hs⟩ := hJ
  have hpq : π ≠ π' := hnb.1
  have heval : ∀ x y, μ (ofGlobal {π, π'} (two π x y)) = J x y := by
    intro x y
    rw [hμ]
    have h1 : ∀ x', x' ≠ x → (∑ y', if ofGlobal {π, π'} (two π x y) =
        ofGlobal {π, π'} (two π x' y') then J x' y' else 0) = 0 :=
      fun x' hx' => sum_eq_zero (fun y' _ => ite_eq_right (fun h => hx' ((two_iff hpq).mp h).1.symm))
    rw [Fintype.sum_eq_single x h1]
    have h2 : ∀ y', y' ≠ y → (if ofGlobal {π, π'} (two π x y) =
        ofGlobal {π, π'} (two π x y') then J x y' else 0) = 0 :=
      fun y' hy' => ite_eq_right (fun h => hy' ((two_iff hpq).mp h).2.symm)
    rw [Fintype.sum_eq_single y h2]
    simp
  have hsup : ∀ ρ, μ ρ ≠ 0 → ∃ x y, J x y ≠ 0 ∧ ρ = ofGlobal {π, π'} (two π x y) := by
    intro ρ h
    rw [hμ] at h
    obtain ⟨x, -, hx⟩ := exists_ne_zero_of_sum_ne_zero h
    obtain ⟨y, -, hy⟩ := exists_ne_zero_of_sum_ne_zero hx
    by_cases he : ρ = ofGlobal {π, π'} (two π x y)
    · rw [ite_eq_left he] at hy; exact ⟨x, y, hy, he⟩
    · rw [ite_eq_right he] at hy; exact absurd rfl hy
  have hform : ∀ ρ, μ ρ ≠ 0 → ∃ f, ρ = ofGlobal {π, π'} f := by
    intro ρ h
    obtain ⟨x, y, -, he⟩ := hsup ρ h
    exact ⟨_, he⟩
  have hmπ : π ∈ ({π, π'} : Finset (Prof ι α)) := mem_insert_self π {π'}
  have hmπ' : π' ∈ ({π, π'} : Finset (Prof ι α)) := mem_insert_of_mem (mem_singleton_self π')
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ρ
    rw [hμ]
    exact sum_nonneg (fun x _ => sum_nonneg (fun y _ => by split_ifs <;> simp [h0 x y]))
  · calc ∑ ρ, μ ρ
        = ∑ ρ, ∑ x, ∑ y, (if ρ = ofGlobal {π, π'} (two π x y) then J x y else 0) :=
          sum_congr rfl (fun ρ _ => hμ ρ)
      _ = ∑ x, ∑ y, ∑ ρ, (if ρ = ofGlobal {π, π'} (two π x y) then J x y else 0) := by
          rw [sum_comm]
          refine sum_congr rfl (fun x _ => ?_)
          rw [sum_comm]
      _ = ∑ x, ∑ y, J x y := by simp
      _ = ∑ x, L π x := by simp_rw [hr]
      _ = 1 := hL1 π
  · intro ρ h
    obtain ⟨x, y, hJxy, hρ⟩ := hsup ρ h
    refine ⟨?_, _, hρ⟩
    intro π₁ h₁ π₂ h₂ k' hnb' x₁ x₂ e₁ e₂
    have v1 : ρ π = some x := by
      rw [hρ, ofGlobal_mem hmπ]; simp [two]
    have v2 : ρ π' = some y := by
      rw [hρ, ofGlobal_mem hmπ']; simp [two, Ne.symm hpq]
    rcases mem_insert.mp h₁ with a1 | a1 <;> rcases mem_insert.mp h₂ with a2 | a2
    · exact absurd (a1.trans a2.symm) hnb'.1
    · rw [mem_singleton] at a2
      rw [a1] at e₁ hnb' ⊢
      rw [a2] at e₂ hnb' ⊢
      have hk : k' = k := nb_unique hnb hnb'.2
      rw [hk]
      rw [v1] at e₁
      rw [v2] at e₂
      rw [← Option.some_injective _ e₁, ← Option.some_injective _ e₂]
      exact hs x y hJxy
    · rw [mem_singleton] at a1
      rw [a1] at e₁ hnb' ⊢
      rw [a2] at e₂ hnb' ⊢
      have hk : k' = k := nb_unique hnb (fun j hj => (hnb'.2 j hj).symm)
      rw [hk]
      rw [v2] at e₁
      rw [v1] at e₂
      rw [← Option.some_injective _ e₁, ← Option.some_injective _ e₂]
      exact admR_swap (hs x y hJxy)
    · rw [mem_singleton] at a1 a2
      exact absurd (a1.trans a2.symm) hnb'.1
  · intro x
    rw [marg_pt hpq hform x]
    simp_rw [heval]
    exact hr x
  · intro x
    have hform' : ∀ ρ, μ ρ ≠ 0 → ∃ f, ρ = ofGlobal {π', π} f := by
      intro ρ h
      obtain ⟨f, hf⟩ := hform ρ h
      exact ⟨f, by rw [hf, pair_comm]⟩
    rw [marg_pt (Ne.symm hpq) hform' x]
    have e : ∀ y, μ (ofGlobal {π', π} (two π' x y)) = J y x := by
      intro y
      rw [pair_comm, two_swap hpq, heval]
    simp_rw [e]
    exact hc x

/-- The empirical model assembled from a choice of representatives and joint draws. -/
noncomputable def eOf
    (rep : (c : Finset (Prof ι α)) → c ∈ (ctxs : Finset (Finset (Prof ι α))) →
      Prof ι α × Prof ι α × ι)
    (J : Prof ι α × Prof ι α × ι → α → α → ℝ) (c : Finset (Prof ι α))
    (ρ : Loc (Prof ι α) α) : ℝ := by
  classical
  exact if hc : c ∈ (ctxs : Finset (Finset (Prof ι α))) then
    ∑ x, ∑ y, if ρ = ofGlobal c (two (rep c hc).1 x y) then J (rep c hc) x y else 0
  else 0

lemma eOf_of_mem
    (rep : (c : Finset (Prof ι α)) → c ∈ (ctxs : Finset (Finset (Prof ι α))) →
      Prof ι α × Prof ι α × ι)
    (J : Prof ι α × Prof ι α × ι → α → α → ℝ) {c : Finset (Prof ι α)}
    (hc : c ∈ (ctxs : Finset (Finset (Prof ι α)))) (ρ : Loc (Prof ι α) α) :
    eOf rep J c ρ =
      ∑ x, ∑ y, if ρ = ofGlobal c (two (rep c hc).1 x y) then J (rep c hc) x y else 0 := by
  unfold eOf
  simp only [hc, ↓reduceDIte]

lemma eOf_of_not_mem
    (rep : (c : Finset (Prof ι α)) → c ∈ (ctxs : Finset (Finset (Prof ι α))) →
      Prof ι α × Prof ι α × ι)
    (J : Prof ι α × Prof ι α × ι → α → α → ℝ) {c : Finset (Prof ι α)}
    (hc : c ∉ (ctxs : Finset (Finset (Prof ι α)))) (ρ : Loc (Prof ι α) α) :
    eOf rep J c ρ = 0 := by
  unfold eOf
  simp [hc]

/-- SD-strategy-proof rules are the marginals of empirical models. -/
theorem model_of_sdsp {L : Prof ι α → α → ℝ} (hL0 : ∀ π a, 0 ≤ L π a)
    (hL1 : ∀ π, ∑ a, L π a = 1) (hsd : SDSPRule L) :
    ∃ e, Model GS e ∧ HasMarginals e L := by
  have hJ' : ∀ p : Prof ι α × Prof ι α × ι, ∃ J : α → α → ℝ, Nb p.2.2 p.1 p.2.1 →
      (∀ a b, 0 ≤ J a b) ∧ (∀ a, ∑ b, J a b = L p.1 a) ∧ (∀ b, ∑ a, J a b = L p.2.1 b) ∧
      (∀ a b, J a b ≠ 0 → Rankings.AdmR (p.1 p.2.2) (p.2.1 p.2.2) a b) := by
    intro p
    by_cases hp : Nb p.2.2 p.1 p.2.1
    · have h := (Rankings.prop1R (fun σ a => hL0 _ a)).mp (hsd p.1 p.2.2)
        (p.1 p.2.2) (p.2.1 p.2.2)
      simp only [Function.update_eq_self, update_nb hp] at h
      obtain ⟨J, hJ⟩ := h
      exact ⟨J, fun _ => hJ⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hp⟩
  choose J hJ using hJ'
  have hrep' : ∀ c ∈ (ctxs : Finset (Finset (Prof ι α))),
      ∃ p : Prof ι α × Prof ι α × ι, Nb p.2.2 p.1 p.2.1 ∧ c = {p.1, p.2.1} := by
    intro c hc
    obtain ⟨π, π', k, h, hc'⟩ := mem_ctxs.mp hc
    exact ⟨(π, π', k), h, hc'⟩
  choose rep hrep using hrep'
  have hloc : ∀ c (hc : c ∈ (ctxs : Finset (Finset (Prof ι α)))),
      (∀ ρ, 0 ≤ eOf rep J c ρ) ∧ ∑ ρ, eOf rep J c ρ = 1 ∧
      (∀ ρ, eOf rep J c ρ ≠ 0 → admGS c ρ ∧ ∃ f, ρ = ofGlobal c f) ∧
      (∀ v ∈ c, ∀ x, marg (eOf rep J c) {v} (ptG v x) = L v x) := by
    intro c hc
    obtain ⟨hnb, hcp⟩ := hrep c hc
    obtain ⟨h1, h2, h3, h4, h5⟩ := local_props hL1 hnb (hJ (rep c hc) hnb) c hcp
      (eOf rep J c) (fun ρ => eOf_of_mem rep J hc ρ)
    refine ⟨h1, h2, h3, fun v hv x => ?_⟩
    rw [hcp] at hv
    rcases mem_insert.mp hv with e | e
    · rw [e]; exact h4 x
    · rw [mem_singleton.mp e]; exact h5 x
  have hpair : ∀ c ∈ (GS : Scenario (Prof ι α) α).ctx, c.card = 2 := by
    intro c hc
    obtain ⟨hnb, hcp⟩ := hrep c hc
    rw [hcp]
    exact card_pair hnb.1
  refine ⟨eOf rep J, ?_, fun c hc v hv x => (hloc c hc).2.2.2 v hv x⟩
  exact {
    nonneg := by
      intro c ρ
      by_cases hc : c ∈ (ctxs : Finset (Finset (Prof ι α)))
      · exact (hloc c hc).1 ρ
      · rw [eOf_of_not_mem rep J hc]
    total := fun c hc => (hloc c hc).2.1
    supp := fun c hc => (hloc c hc).2.2.1
    compat := compat_of_pairs GS hpair (fun c hc => (hloc c hc).2.1)
      (fun c hc ρ h => ((hloc c hc).2.2.1 ρ h).2) L (fun c hc => (hloc c hc).2.2.2) }

/-! ### From an empirical model to SD-strategy-proofness -/

theorem sdsp_of_model {L : Prof ι α → α → ℝ} (hL0 : ∀ π a, 0 ≤ L π a)
    {e : Finset (Prof ι α) → Loc (Prof ι α) α → ℝ} (hM : Model GS e) (hm : HasMarginals e L) :
    SDSPRule L := by
  intro π k
  apply (Rankings.prop1R (fun σ a => hL0 _ a)).mpr
  intro ρ τ
  show Rankings.JointDrawR ρ τ (L (Function.update π k ρ)) (L (Function.update π k τ))
  by_cases hρτ : ρ = τ
  · rw [← hρτ]
    refine ⟨fun a b => if a = b then L (Function.update π k ρ) a else 0, ?_, ?_, ?_, ?_⟩
    · intro a b
      by_cases h : a = b
      · simp [h, hL0]
      · simp [h]
    · intro a; simp
    · intro b; simp
    · intro a b h
      by_cases hab : a = b
      · exact ⟨Or.inl hab, Or.inl hab.symm⟩
      · simp [hab] at h
  · obtain ⟨π₁, h₁⟩ : ∃ π₁, π₁ = Function.update π k ρ := ⟨_, rfl⟩
    obtain ⟨π₂, h₂⟩ : ∃ π₂, π₂ = Function.update π k τ := ⟨_, rfl⟩
    rw [← h₁, ← h₂]
    have hnb : Nb k π₁ π₂ := by rw [h₁, h₂]; exact nb_update π k hρτ
    have hk1 : π₁ k = ρ := by rw [h₁]; simp
    have hk2 : π₂ k = τ := by rw [h₂]; simp
    have hpq : π₁ ≠ π₂ := hnb.1
    have hc : ({π₁, π₂} : Finset (Prof ι α)) ∈ (ctxs : Finset (Finset (Prof ι α))) :=
      mem_ctxs.mpr ⟨π₁, π₂, k, hnb, rfl⟩
    have hm1 : π₁ ∈ ({π₁, π₂} : Finset (Prof ι α)) := mem_insert_self π₁ {π₂}
    have hm2 : π₂ ∈ ({π₁, π₂} : Finset (Prof ι α)) := mem_insert_of_mem (mem_singleton_self π₂)
    have hs : ∀ ρ', e {π₁, π₂} ρ' ≠ 0 → ∃ f, ρ' = ofGlobal {π₁, π₂} f :=
      fun ρ' h => (hM.supp _ hc ρ' h).2
    have hs' : ∀ ρ', e {π₁, π₂} ρ' ≠ 0 → ∃ f, ρ' = ofGlobal {π₂, π₁} f := by
      intro ρ' h
      obtain ⟨f, hf⟩ := hs ρ' h
      exact ⟨f, by rw [hf, pair_comm]⟩
    refine ⟨fun x y => e {π₁, π₂} (ofGlobal {π₁, π₂} (two π₁ x y)), ?_, ?_, ?_, ?_⟩
    · intro x y; exact hM.nonneg _ _
    · intro x
      show ∑ y, e {π₁, π₂} (ofGlobal {π₁, π₂} (two π₁ x y)) = L π₁ x
      rw [← marg_pt hpq hs x]
      exact hm _ hc π₁ hm1 x
    · intro y
      have e1 : ∀ x, e {π₁, π₂} (ofGlobal {π₁, π₂} (two π₁ x y)) =
          e {π₁, π₂} (ofGlobal {π₂, π₁} (two π₂ y x)) := by
        intro x
        rw [pair_comm π₂ π₁, two_swap hpq]
      show ∑ x, e {π₁, π₂} (ofGlobal {π₁, π₂} (two π₁ x y)) = L π₂ y
      simp_rw [e1]
      rw [← marg_pt (Ne.symm hpq) hs' y]
      exact hm _ hc π₂ hm2 y
    · intro x y h
      have hadm := (hM.supp _ hc _ h).1
      have v1 : ofGlobal {π₁, π₂} (two π₁ x y) π₁ = some x := by
        rw [ofGlobal_mem hm1]; simp [two]
      have v2 : ofGlobal {π₁, π₂} (two π₁ x y) π₂ = some y := by
        rw [ofGlobal_mem hm2]; simp [two, Ne.symm hpq]
      have := hadm π₁ hm1 π₂ hm2 k hnb x y v1 v2
      rw [hk1, hk2] at this
      exact this

/-- Proposition 1 of *Gibbard–Satterthwaite as a Scenario*: the families of one-profile marginals
of empirical models of the scenario are exactly the SD-strategy-proof random rules. -/
theorem gs_prop1 {L : Prof ι α → α → ℝ} (hL0 : ∀ π a, 0 ≤ L π a) (hL1 : ∀ π, ∑ a, L π a = 1) :
    (∃ e, Model GS e ∧ HasMarginals e L) ↔ SDSPRule L :=
  ⟨fun ⟨_, hM, hm⟩ => sdsp_of_model hL0 hM hm, model_of_sdsp hL0 hL1⟩

end GSScenario

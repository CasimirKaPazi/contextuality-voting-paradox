module

public import Mathlib
public import GSScenario

@[expose] public section

/-!
# The random top two: a contextual model without unanimity

*Gibbard–Satterthwaite as a Scenario*, Proposition 3, for one voter (`ι = Unit`) in the scenario of
`GSScenario.lean` (no boundary condition).

The random top two gives the voter's first and second choice with probability ½ each
(`topTwo`).

* `topTwo_model` (two or more alternatives): there is an empirical model with full compatibility
  whose one-profile marginals are the random top two. The scheme is SD-strategy-proof
  (`sdsp_topTwoB`), so `GSScenario.gs_prop1` applies.
* `topTwo_contextual` (three or more alternatives): no family of context distributions with
  these marginals is non-contextual. Suppose a distribution `d` on global sections had them.
  A weighted global section chooses from the top two of every ballot; one that gives the second
  choice `b` under a ballot with top `a` never gives `a` (a global section gives the best
  element of its range); so the weight of the sections that never give `a` is ½, for every `a`.
  No weighted section misses two alternatives, so these weights sum to at most 1, but they sum
  to (number of alternatives)/2.
-/

open Finset Scenarios GSScenario

namespace GSTopTwo

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Positions in a ranking -/

lemma pos_lt_card (σ : PathPinning.Rk α) (x : α) : Rankings.pos σ x < Fintype.card α := by
  unfold Rankings.pos
  have hsub : Rankings.above σ x ⊆ univ.erase x := by
    intro c hc
    simp only [Rankings.above, mem_filter, mem_univ, true_and] at hc
    refine mem_erase.mpr ⟨?_, mem_univ c⟩
    rintro rfl
    simp [PathPinning.irrefl] at hc
  calc (Rankings.above σ x).card ≤ (univ.erase x).card := card_le_card hsub
    _ < Fintype.card α := by
      rw [card_erase_of_mem (mem_univ x), card_univ]
      exact Nat.sub_lt (Fintype.card_pos_iff.mpr ⟨x⟩) one_pos

/-- Every position below the number of alternatives is taken. -/
lemma pos_surj (σ : PathPinning.Rk α) {k : ℕ} (hk : k < Fintype.card α) :
    ∃ x, Rankings.pos σ x = k := by
  have himg : univ.image (Rankings.pos σ) = range (Fintype.card α) := by
    apply eq_of_subset_of_card_le
    · intro n hn
      obtain ⟨x, -, rfl⟩ := mem_image.mp hn
      exact mem_range.mpr (pos_lt_card σ x)
    · rw [card_range, card_image_of_injective _ (Rankings.pos_inj σ), card_univ]
  have hk' : k ∈ univ.image (Rankings.pos σ) := by
    rw [himg]
    exact mem_range.mpr hk
  obtain ⟨x, -, hx⟩ := mem_image.mp hk'
  exact ⟨x, hx⟩

lemma pos_toRk (h : α → ℕ) (hh : Function.Injective h) (x : α) :
    Rankings.pos (Rankings.toRk h hh) x = (univ.filter (fun c => h c < h x)).card := by
  unfold Rankings.pos Rankings.above
  congr 1

/-! ### The random top two -/

/-- First and second choice with probability ½ each. -/
noncomputable def topTwoB (ρ : PathPinning.Rk α) (x : α) : ℝ :=
  if Rankings.pos ρ x < 2 then 1 / 2 else 0

/-- The random top two as a rule for one voter. -/
noncomputable def topTwo (π : Prof Unit α) (x : α) : ℝ := topTwoB (π ()) x

lemma topTwoB_nonneg (ρ : PathPinning.Rk α) (x : α) : 0 ≤ topTwoB ρ x := by
  unfold topTwoB; split_ifs <;> norm_num

lemma topTwoB_le (ρ : PathPinning.Rk α) (x : α) : topTwoB ρ x ≤ 1 / 2 := by
  unfold topTwoB; split_ifs <;> norm_num

lemma topTwoB_sum (h2 : 2 ≤ Fintype.card α) (σ : PathPinning.Rk α) : ∑ x, topTwoB σ x = 1 := by
  obtain ⟨y0, h0⟩ := pos_surj σ (k := 0) (by omega)
  obtain ⟨y1, h1⟩ := pos_surj σ (k := 1) (by omega)
  have hne : y0 ≠ y1 := fun e => by rw [e] at h0; omega
  have hfil : univ.filter (fun x => Rankings.pos σ x < 2) = {y0, y1} := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · intro hx
      rcases (by omega : Rankings.pos σ x = 0 ∨ Rankings.pos σ x = 1) with e | e
      · left; exact Rankings.pos_inj σ (e.trans h0.symm)
      · right; exact Rankings.pos_inj σ (e.trans h1.symm)
    · rintro (rfl | rfl) <;> omega
  unfold topTwoB
  rw [← sum_filter, hfil, sum_pair hne]
  norm_num

/-- The random top two is SD-strategy-proof. -/
lemma sdsp_topTwoB (h2 : 2 ≤ Fintype.card α) : Rankings.SDSPR (topTwoB (α := α)) := by
  intro ρ τ U hU
  by_cases hA : ∃ x ∈ U, 2 ≤ Rankings.pos ρ x
  · obtain ⟨x, hxU, hx⟩ := hA
    have hin : ∀ y, Rankings.pos ρ y < 2 → y ∈ U := fun y hy =>
      hU y x hxU ((Rankings.pos_lt_iff ρ y x).mp (by omega))
    have hρ : ∑ a ∈ U, topTwoB ρ a = 1 := by
      rw [← topTwoB_sum h2 ρ]
      apply sum_subset (subset_univ U)
      intro y _ hy
      unfold topTwoB
      exact ite_eq_right (fun h => hy (hin y h))
    rw [hρ, ← topTwoB_sum h2 τ]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ U) (fun y _ _ => topTwoB_nonneg τ y)
  · push Not at hA
    apply sum_le_sum
    intro x hx
    have e : topTwoB ρ x = 1 / 2 := by
      unfold topTwoB
      exact ite_eq_left (hA x hx)
    rw [e]
    exact topTwoB_le τ x

lemma sdspRule_topTwo (h2 : 2 ≤ Fintype.card α) : SDSPRule (topTwo (α := α)) := by
  intro π k
  cases k
  have e : (fun σ => topTwo (Function.update π () σ)) = topTwoB := by
    funext σ x
    simp [topTwo]
  rw [e]
  exact sdsp_topTwoB h2

/-- Proposition 3, first part: the random top two is the family of marginals of an empirical
model. -/
theorem topTwo_model (h2 : 2 ≤ Fintype.card α) :
    ∃ e, Model (GS : Scenario (Prof Unit α) α) e ∧ HasMarginals e topTwo :=
  (gs_prop1 (L := topTwo) (fun π a => topTwoB_nonneg (π ()) a)
    (fun π => topTwoB_sum h2 (π ()))).mpr (sdspRule_topTwo h2)

/-! ### Ballots with a prescribed top two -/

/-- An injective numbering of the alternatives. -/
noncomputable def emb (α : Type*) [Fintype α] : α → ℕ := fun c => ((Fintype.equivFin α) c : ℕ)

omit [DecidableEq α] in
lemma emb_inj : Function.Injective (emb α) :=
  fun _ _ h => (Fintype.equivFin α).injective (Fin.ext h)

/-- Positions: `a` first, `b` second, the rest after. -/
noncomputable def hmap (a b : α) : α → ℕ :=
  fun c => if c = a then 0 else if c = b then 1 else emb α c + 2

lemma hmap_inj (a b : α) : Function.Injective (hmap a b) := by
  intro c c' h
  unfold hmap at h
  split_ifs at h <;>
    first
    | (subst_vars; rfl)
    | exact absurd h (by omega)
    | exact emb_inj (by omega)

/-- The ballot `a b (rest)`. -/
noncomputable def ballot (a b : α) : PathPinning.Rk α := Rankings.toRk (hmap a b) (hmap_inj a b)

lemma ballot_ab {a b : α} (hab : a ≠ b) : (ballot a b).1 a b = true := by
  unfold ballot
  rw [Rankings.toRk_apply]
  simp [hmap, Ne.symm hab]

lemma top2_ballot {a b : α} (hab : a ≠ b) (x : α) :
    Rankings.pos (ballot a b) x < 2 ↔ x = a ∨ x = b := by
  unfold ballot
  rw [pos_toRk]
  constructor
  · intro hx
    by_contra hno
    push Not at hno
    have hsub : ({a, b} : Finset α) ⊆ univ.filter (fun c => hmap a b c < hmap a b x) := by
      intro c hc
      simp only [mem_insert, mem_singleton] at hc
      simp only [mem_filter, mem_univ, true_and]
      rcases hc with h | h <;> rw [h]
      · simp [hmap, hno.1, hno.2]
      · simp [hmap, hno.1, hno.2, Ne.symm hab]
    have hc := card_le_card hsub
    rw [card_pair hab] at hc
    omega
  · rintro (h | h) <;> rw [h]
    · have hE : univ.filter (fun c => hmap a b c < hmap a b a) = ∅ := by
        apply filter_false_of_mem
        intro c _
        simp [hmap]
      rw [hE, card_empty]
      omega
    · have hsub : univ.filter (fun c => hmap a b c < hmap a b b) ⊆ {a} := by
        intro c hc
        simp only [mem_filter, mem_univ, true_and] at hc
        rw [mem_singleton]
        by_contra hca
        have hb : hmap a b b = 1 := by simp [hmap, Ne.symm hab]
        rw [hb] at hc
        unfold hmap at hc
        rw [ite_eq_right hca] at hc
        split_ifs at hc <;> omega
      have hc := card_le_card hsub
      rw [card_singleton] at hc
      omega

/-- Every profile of one voter has another one. -/
lemma exists_other (h2 : 2 ≤ Fintype.card α) (π : Prof Unit α) : ∃ π', π ≠ π' := by
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card α)
  have hdiff : (fun _ : Unit => ballot a b) ≠ (fun _ : Unit => ballot b a) := by
    intro h
    have h1 := ballot_ab hab
    have h2' := ballot_ab (Ne.symm hab)
    have e : ballot a b = ballot b a := congrFun h ()
    rw [e, PathPinning.asymm _ h2'] at h1
    exact Bool.false_ne_true h1
  by_cases hπ : π = fun _ => ballot a b
  · exact ⟨fun _ => ballot b a, by rw [hπ]; exact hdiff⟩
  · exact ⟨fun _ => ballot a b, hπ⟩

/-! ### Global sections and marginals -/

lemma nb_unit {π π' : Prof Unit α} (hne : π ≠ π') : Nb () π π' :=
  ⟨hne, fun j hj => (hj (Subsingleton.elim j ())).elim⟩

lemma global_adm {f : Prof Unit α → α} (hf : IsGlobal (GS : Scenario (Prof Unit α) α) f)
    {π π' : Prof Unit α} (hne : π ≠ π') :
    Rankings.AdmR (π ()) (π' ()) (f π) (f π') := by
  have hc : ({π, π'} : Finset (Prof Unit α)) ∈ (ctxs : Finset (Finset (Prof Unit α))) :=
    mem_ctxs.mpr ⟨π, π', (), nb_unit hne, rfl⟩
  have hm1 : π ∈ ({π, π'} : Finset (Prof Unit α)) := mem_insert_self π {π'}
  have hm2 : π' ∈ ({π, π'} : Finset (Prof Unit α)) := mem_insert_of_mem (mem_singleton_self π')
  exact hf _ hc π hm1 π' hm2 () (nb_unit hne) (f π) (f π')
    (ofGlobal_mem hm1) (ofGlobal_mem hm2)

lemma marg_d {e : Finset (Prof Unit α) → Loc (Prof Unit α) α → ℝ} {d : (Prof Unit α → α) → ℝ}
    (hde : ∀ c ∈ (GS : Scenario (Prof Unit α) α).ctx, ∀ ρ, e c ρ = mix d c ρ)
    (hm : HasMarginals e topTwo) {π π' : Prof Unit α} (hne : π ≠ π') (x : α) :
    ∑ f ∈ univ.filter (fun f : Prof Unit α → α => f π = x), d f = topTwo π x := by
  have hc : ({π, π'} : Finset (Prof Unit α)) ∈ (ctxs : Finset (Finset (Prof Unit α))) :=
    mem_ctxs.mpr ⟨π, π', (), nb_unit hne, rfl⟩
  have hmem : π ∈ ({π, π'} : Finset (Prof Unit α)) := mem_insert_self π {π'}
  have h1 := hm _ hc π hmem x
  have he : e {π, π'} = mix d {π, π'} := funext (hde _ hc)
  rw [he, marg_mix, singleton_inter_of_mem hmem] at h1
  rw [← h1]
  refine sum_congr ?_ (fun _ _ => rfl)
  ext f
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro hf
    exact ofGlobal_eq_of (fun v hv => by rw [mem_singleton.mp hv, hf])
  · intro hf
    have h' := congrFun hf π
    rw [ptG, ofGlobal_mem (mem_singleton_self π), ofGlobal_mem (mem_singleton_self π)] at h'
    exact Option.some_injective _ h'

/-- The global assignment `f` never gives `a`. -/
def Miss (f : Prof Unit α → α) (a : α) : Prop := ∀ π, f π ≠ a

/-- Proposition 3, second part: no family with the random top two as marginals is
non-contextual. -/
theorem topTwo_contextual (h3 : 3 ≤ Fintype.card α)
    {e : Finset (Prof Unit α) → Loc (Prof Unit α) α → ℝ} (hm : HasMarginals e topTwo) :
    ¬ NonContextual (GS : Scenario (Prof Unit α) α) e := by
  classical
  rintro ⟨d, hd0, hd1, hdg, hde⟩
  have h2 : 2 ≤ Fintype.card α := by omega
  let pr : PathPinning.Rk α → Prof Unit α := fun ρ _ => ρ
  have hstar : ∀ (π : Prof Unit α) x,
      ∑ f ∈ univ.filter (fun f : Prof Unit α → α => f π = x), d f = topTwo π x := by
    intro π x
    obtain ⟨π', hne⟩ := exists_other h2 π
    exact marg_d hde hm hne x
  -- a weighted global section chooses from the top two of every ballot
  have stepA : ∀ f, d f ≠ 0 → ∀ π : Prof Unit α, Rankings.pos (π ()) (f π) < 2 := by
    intro f hf π
    by_contra hge
    have h0 : topTwo π (f π) = 0 := by
      unfold topTwo topTwoB
      exact ite_eq_right hge
    have hs := hstar π (f π)
    rw [h0, sum_eq_zero_iff_of_nonneg (fun g _ => hd0 g)] at hs
    exact hf (hs f (mem_filter.mpr ⟨mem_univ f, rfl⟩))
  -- no weighted section misses two alternatives
  have stepD : ∀ f, d f ≠ 0 → ∀ a a' : α, a ≠ a' → Miss f a → Miss f a' → False := by
    intro f hf a a' haa ha ha'
    have := (top2_ballot haa (f (pr (ballot a a')))).mp (stepA f hf (pr (ballot a a')))
    rcases this with h | h
    · exact ha _ h
    · exact ha' _ h
  -- the sections that never give `a` have weight ½
  have hmissSum : ∀ a : α, ∑ f, (if Miss f a then d f else 0) = 1 / 2 := by
    intro a
    obtain ⟨b, hba⟩ : ∃ b, b ≠ a := by
      obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card α)
      by_cases hx : x = a
      · exact ⟨y, fun h => hxy (hx.trans h.symm)⟩
      · exact ⟨x, hx⟩
    have hab : a ≠ b := Ne.symm hba
    have hs := hstar (pr (ballot a b)) b
    have hL : topTwo (pr (ballot a b)) b = 1 / 2 := by
      unfold topTwo topTwoB
      exact ite_eq_left ((top2_ballot hab b).mpr (Or.inr rfl))
    rw [hL, sum_filter] at hs
    rw [← hs]
    refine sum_congr rfl (fun f _ => ?_)
    by_cases hf : d f = 0
    · simp [hf]
    · have key : f (pr (ballot a b)) = b ↔ Miss f a := by
        constructor
        · intro hfb π hπa
          by_cases hπ : pr (ballot a b) = π
          · rw [hπ] at hfb
            exact hba (hfb.symm.trans hπa)
          · have hadm := global_adm (hdg f hf) hπ
            rw [hfb, hπa] at hadm
            rcases hadm.1 with h | h
            · exact hba h
            · have h' : (ballot a b).1 b a = true := h
              rw [PathPinning.asymm _ (ballot_ab hab)] at h'
              exact Bool.false_ne_true h'
        · intro hmiss
          rcases (top2_ballot hab (f (pr (ballot a b)))).mp (stepA f hf (pr (ballot a b))) with
            h | h
          · exact absurd h (hmiss _)
          · exact h
      by_cases hb : f (pr (ballot a b)) = b
      · rw [ite_eq_left (key.mp hb), ite_eq_left hb]
      · rw [ite_eq_right (fun h => hb (key.mpr h)), ite_eq_right hb]
  -- these weights sum to at most one
  have hsum_le : ∑ a, ∑ f, (if Miss f a then d f else 0) ≤ 1 := by
    rw [sum_comm, ← hd1]
    apply sum_le_sum
    intro f _
    by_cases hf : d f = 0
    · simp [hf]
    · by_cases hex : ∃ a, Miss f a
      · obtain ⟨a0, ha0⟩ := hex
        have h0 : ∀ a, a ≠ a0 → (if Miss f a then d f else 0) = 0 :=
          fun a ha => ite_eq_right (fun hma => stepD f hf a a0 ha hma ha0)
        exact le_of_eq (by rw [Fintype.sum_eq_single a0 h0, ite_eq_left ha0])
      · push Not at hex
        rw [sum_eq_zero (fun a _ => ite_eq_right (hex a))]
        exact hd0 f
  have hall : ∑ a, ∑ f, (if Miss f a then d f else 0) = (Fintype.card α : ℝ) * (1 / 2) := by
    simp_rw [hmissSum]
    simp
  rw [hall] at hsum_le
  have h3' : (3 : ℝ) ≤ Fintype.card α := by exact_mod_cast h3
  linarith

end GSTopTwo

/-
  Proposition 4 of *Bounds from Criteria*
  (`notes/strategic-information/bounds.md`, Section 4): the odd functions in
  the row space of the strategic count have dimension d − e.

  Setting. Types T with an opposite type `opp t`. A function r on types is a
  row: what a voter of each type adds. Its even part is
  ½ (r(t) + r(opp t)) (`ev`), and r is odd if its even part is constant. The
  row space V is any subspace of functions on types that contains the
  constants (for a strategic count, the span of its rows and the size of the
  electorate). Write d + 1 for its dimension and e + 1 for that of the even
  parts of its members, so that d and e do not count constants.

  * `odd_eq_sup`: the odd functions in V are the kernel of the even part on V
    plus the constants.
  * `prop4`: dim(odd functions in V) + dim(even parts of V) = dim V + 1, that
    is, the odd functions in V have dimension d − e, not counting constants.
  * `odd_lt`: if some member of V is not odd, the odd functions in V have
    smaller dimension than V.
-/

module

public import Mathlib

@[expose] public section

open Module

namespace OppositeVoters

variable {T : Type*} [Fintype T] (opp : T → T)

/-- The even part of a function on types. -/
def ev : (T → ℚ) →ₗ[ℚ] (T → ℚ) := (1 / 2 : ℚ) • (LinearMap.id + LinearMap.funLeft ℚ ℚ opp)

omit [Fintype T] in
lemma ev_apply (r : T → ℚ) (t : T) : ev opp r t = (r t + r (opp t)) / 2 := by
  simp only [ev, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.funLeft_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

omit [Fintype T] in
lemma ev_one : ev opp (1 : T → ℚ) = 1 := by
  funext t
  rw [ev_apply]
  simp only [Pi.one_apply]
  norm_num

/-- The constant functions. -/
def consts : Submodule ℚ (T → ℚ) := Submodule.span ℚ {1}

/-- The odd functions in V: those whose even part is constant. -/
def odd (V : Submodule ℚ (T → ℚ)) : Submodule ℚ (T → ℚ) :=
  V ⊓ (consts (T := T)).comap (ev opp)

omit [Fintype T] in
/-- The odd functions in V are the kernel of the even part on V plus the
    constants. -/
theorem odd_eq_sup (V : Submodule ℚ (T → ℚ)) (h1 : (1 : T → ℚ) ∈ V) :
    odd opp V = (V ⊓ LinearMap.ker (ev opp)) ⊔ consts := by
  ext r
  simp only [odd, consts, Submodule.mem_inf, Submodule.mem_comap, Submodule.mem_sup,
    LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨hV, c, hc⟩
    refine ⟨r - c • 1, ⟨V.sub_mem hV (V.smul_mem c h1), ?_⟩, c • 1, ⟨c, rfl⟩, sub_add_cancel r _⟩
    rw [map_sub, map_smul, ev_one, hc, sub_self]
  · rintro ⟨y, ⟨hyV, hy⟩, z, ⟨c, rfl⟩, rfl⟩
    refine ⟨V.add_mem hyV (V.smul_mem c h1), c, ?_⟩
    rw [map_add, hy, zero_add, map_smul, ev_one]

/-- The kernel of the even part on V has dimension dim V − dim ev(V). -/
lemma finrank_ker (V : Submodule ℚ (T → ℚ)) :
    finrank ℚ (V.map (ev opp)) + finrank ℚ ↥(V ⊓ LinearMap.ker (ev opp)) = finrank ℚ V := by
  have h := LinearMap.finrank_range_add_finrank_ker ((ev opp).domRestrict V)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  rw [← h]
  congr 1
  have e1 : (LinearMap.ker (ev opp)).comap V.subtype =
      (V ⊓ LinearMap.ker (ev opp)).comap V.subtype := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
  rw [e1]
  exact (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe inf_le_left)).symm

/-- **Proposition 4.** dim(odd functions in V) + dim(even parts of V) = dim V + 1. -/
theorem prop4 [Nonempty T] (V : Submodule ℚ (T → ℚ)) (h1 : (1 : T → ℚ) ∈ V) :
    finrank ℚ (odd opp V) + finrank ℚ (V.map (ev opp)) = finrank ℚ V + 1 := by
  have hne : (1 : T → ℚ) ≠ 0 := fun h => by
    have := congr_fun h (Classical.arbitrary T)
    simp at this
  have hnot : (1 : T → ℚ) ∉ V ⊓ LinearMap.ker (ev opp) := fun h => by
    have := (Submodule.mem_inf.mp h).2
    rw [LinearMap.mem_ker, ev_one] at this
    exact hne this
  have hbot : (V ⊓ LinearMap.ker (ev opp)) ⊓ consts = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    obtain ⟨hA, hB⟩ := Submodule.mem_inf.mp hr
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hB
    by_cases hc : c = 0
    · simp [hc]
    · have h1' : (1 : T → ℚ) ∈ V ⊓ LinearMap.ker (ev opp) := by
        have := (V ⊓ LinearMap.ker (ev opp)).smul_mem c⁻¹ hA
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
      exact absurd h1' hnot
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (V ⊓ LinearMap.ker (ev opp))
    (consts (T := T))
  rw [hbot, finrank_bot, add_zero, consts, finrank_span_singleton hne] at hsup
  rw [odd_eq_sup opp V h1, consts, hsup, ← finrank_ker opp V]
  ring

/-- If some member of V is not odd, the odd functions in V have smaller
    dimension than V. -/
theorem odd_lt [Nonempty T] (V : Submodule ℚ (T → ℚ)) (h1 : (1 : T → ℚ) ∈ V)
    (hnot : ¬ V ≤ odd opp V) : finrank ℚ (odd opp V) < finrank ℚ V := by
  have h4 := prop4 opp V h1
  -- the even parts contain the constants and something more
  have hc : consts ≤ V.map (ev opp) := by
    rw [consts, Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨1, h1, ev_one opp⟩
  have hne : consts ≠ V.map (ev opp) := by
    intro heq
    apply hnot
    intro r hr
    refine ⟨hr, ?_⟩
    show ev opp r ∈ consts
    rw [heq]
    exact ⟨r, hr, rfl⟩
  have hlt : finrank ℚ (consts (T := T)) < finrank ℚ (V.map (ev opp)) :=
    Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hc hne)
  have hone : finrank ℚ (consts (T := T)) = 1 := by
    rw [consts]
    exact finrank_span_singleton fun h => by
      have := congr_fun h (Classical.arbitrary T)
      simp at this
  omega

end OppositeVoters

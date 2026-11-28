/-
  Propositions 2 and 4 of *The Ballot Polytope*
  (`notes/strategic-information/ballot-polytope.md`, Sections 2 and 4), in
  the linear regime: the value of a ballot is g · τ(b) for the gradient g, a
  linear function on the space E of count vectors, and S is the finite set of
  count vectors of the ballots. The ballot polytope is the convex hull of S;
  its vertices are the extreme points of the hull.

  * `IsUniqueMax g S s`: s is in S and every other point of S has a smaller
    value of g; a voter with gradient g has the unique best reply s.
  * `prop2_unique` (Proposition 2, part 1, the unique case): a unique best
    reply is a vertex. The points of the hull with value at least g(s) are s
    alone (`eq_of_unique`), since s together with the points of smaller value
    is a convex set containing S.
  * `prop2_not_vertex` (Proposition 2, part 2): a count vector that is not a
    vertex is a unique best reply for no gradient.
  * `prop4` (Proposition 4): if the count vectors are symmetric about c/2
    (`Sym S c`), the unique best reply for −g is c − s when that for g is s,
    so opposite voters add c together. `sym_of_reverse`: if a ballot and its
    reverse always add c, as the Equality Criterion asks, the count vectors
    are symmetric. `prop4_conv`: conversely, if the unique best replies for g
    and −g always add up to c, then with every vertex that is a unique best
    reply also c minus it is a count vector, and a vertex.

  Not here: that some best reply is a vertex when the best reply is not
  unique (a face argument), and Proposition 2, part 3, that every vertex is
  the unique best reply for some gradient (separation). The converse of
  Proposition 4 is stated for vertices that are unique best replies.
-/

module

public import Mathlib

@[expose] public section

open Finset

namespace BallotPolytope

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- s is the unique maximiser of g on S. -/
def IsUniqueMax (g : E →ₗ[ℝ] ℝ) (S : Finset E) (s : E) : Prop :=
  s ∈ S ∧ ∀ t ∈ S, t ≠ s → g t < g s

/-! ### Proposition 2 -/

lemma le_on_hull (g : E →ₗ[ℝ] ℝ) (S : Finset E) {M : ℝ} (hM : ∀ t ∈ S, g t ≤ M) {x : E}
    (hx : x ∈ convexHull ℝ (S : Set E)) : g x ≤ M :=
  convexHull_min (fun t ht => hM t ht) (convex_halfSpace_le g.isLinear M) hx

/-- s with the points of smaller value is convex. -/
lemma convex_below (g : E →ₗ[ℝ] ℝ) (s : E) : Convex ℝ {x : E | x = s ∨ g x < g s} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hgs : a * g s + b * g s = g s := by rw [← add_mul, hab, one_mul]
  have hval : g (a • x + b • y) = a * g x + b * g y := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · left
    rw [hx, hy]
    exact Convex.combo_self hab s
  · rcases eq_or_lt_of_le hb with hb0 | hbpos
    · left
      have ha1 : a = 1 := by linarith
      rw [← hb0, ha1, zero_smul, add_zero, one_smul, hx]
    · right
      rw [hval, hx]
      have h1 : b * g y < b * g s := mul_lt_mul_of_pos_left hy hbpos
      linarith
  · rcases eq_or_lt_of_le ha with ha0 | hapos
    · left
      have hb1 : b = 1 := by linarith
      rw [← ha0, hb1, zero_smul, zero_add, one_smul, hy]
    · right
      rw [hval, hy]
      have h1 : a * g x < a * g s := mul_lt_mul_of_pos_left hx hapos
      linarith
  · right
    rw [hval]
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · have hb1 : b = 1 := by linarith
      rw [← ha0, hb1]
      linarith
    · have h1 : a * g x < a * g s := mul_lt_mul_of_pos_left hx hapos
      have h2 : b * g y ≤ b * g s := mul_le_mul_of_nonneg_left hy.le hb
      linarith

/-- The only point of the hull with value at least g(s) is s. -/
lemma eq_of_unique {g : E →ₗ[ℝ] ℝ} {S : Finset E} {s : E} (h : IsUniqueMax g S s) {x : E}
    (hx : x ∈ convexHull ℝ (S : Set E)) (hgx : g s ≤ g x) : x = s := by
  have hsub : (S : Set E) ⊆ {x : E | x = s ∨ g x < g s} := fun t ht => by
    by_cases hts : t = s
    · exact Or.inl hts
    · exact Or.inr (h.2 t ht hts)
  rcases convexHull_min hsub (convex_below g s) hx with hxs | hlt
  · exact hxs
  · exact absurd hgx (not_le.mpr hlt)

/-- **Proposition 2, part 1.** A unique best reply is a vertex. -/
theorem prop2_unique {g : E →ₗ[ℝ] ℝ} {S : Finset E} {s : E} (h : IsUniqueMax g S s) :
    s ∈ (convexHull ℝ (S : Set E)).extremePoints ℝ := by
  have hle : ∀ t ∈ S, g t ≤ g s := fun t ht => by
    by_cases hts : t = s
    · rw [hts]
    · exact (h.2 t ht hts).le
  rw [mem_extremePoints]
  refine ⟨subset_convexHull ℝ _ h.1, fun x hx y hy hseg => ?_⟩
  obtain ⟨a, b, ha, hb, hab, hxy⟩ := hseg
  have hgx := le_on_hull g S hle hx
  have hgy := le_on_hull g S hle hy
  have hval : g s = a * g x + b * g y := by
    rw [← hxy, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hgs : a * g s + b * g s = g s := by rw [← add_mul, hab, one_mul]
  have hx' : g s ≤ g x := by
    by_contra hlt
    push Not at hlt
    have h1 : a * g x < a * g s := mul_lt_mul_of_pos_left hlt ha
    have h2 : b * g y ≤ b * g s := mul_le_mul_of_nonneg_left hgy hb.le
    linarith
  have hy' : g s ≤ g y := by
    by_contra hlt
    push Not at hlt
    have h1 : b * g y < b * g s := mul_lt_mul_of_pos_left hlt hb
    have h2 : a * g x ≤ a * g s := mul_le_mul_of_nonneg_left hgx ha.le
    linarith
  exact ⟨eq_of_unique h hx hx', eq_of_unique h hy hy'⟩

/-- **Proposition 2, part 2.** A count vector that is not a vertex is the
    unique best reply for no gradient. -/
theorem prop2_not_vertex {S : Finset E} {s : E}
    (hs : s ∉ (convexHull ℝ (S : Set E)).extremePoints ℝ) (g : E →ₗ[ℝ] ℝ) :
    ¬ IsUniqueMax g S s := fun h => hs (prop2_unique h)

/-! ### Proposition 4 -/

/-- The count vectors are symmetric about c/2. -/
def Sym (S : Finset E) (c : E) : Prop := ∀ v ∈ S, c - v ∈ S

omit [Module ℝ E] in
/-- If a ballot and its reverse always add c, the count vectors are
    symmetric. -/
theorem sym_of_reverse {Bal : Type*} [DecidableEq E] (τ : Bal → E) (rev : Bal → Bal)
    (B : Finset Bal) (hB : ∀ b ∈ B, rev b ∈ B) {c : E} (hc : ∀ b, τ b + τ (rev b) = c) :
    Sym (B.image τ) c := by
  intro v hv
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
  refine Finset.mem_image.mpr ⟨rev b, hB b hb, ?_⟩
  rw [← hc b]
  abel

/-- **Proposition 4.** On a symmetric set of count vectors, the unique best
    reply for −g is c − s when that for g is s: opposite voters add c. -/
theorem prop4 {S : Finset E} {c : E} (hS : Sym S c) {g : E →ₗ[ℝ] ℝ} {s : E}
    (h : IsUniqueMax g S s) : IsUniqueMax (-g) S (c - s) := by
  refine ⟨hS s h.1, fun t ht hts => ?_⟩
  have hct : c - t ≠ s := fun e => hts (by rw [← e]; abel)
  have := h.2 (c - t) (hS t ht) hct
  simp only [LinearMap.neg_apply, map_sub] at this ⊢
  linarith

/-- **Proposition 4, converse.** If the unique best replies for g and −g
    always add up to c, then with every unique best reply v also c − v is a
    count vector, and a vertex. -/
theorem prop4_conv {S : Finset E} {c : E}
    (hconv : ∀ (g : E →ₗ[ℝ] ℝ) s, IsUniqueMax g S s → ∃ s', IsUniqueMax (-g) S s' ∧ s + s' = c)
    {g : E →ₗ[ℝ] ℝ} {v : E} (h : IsUniqueMax g S v) :
    c - v ∈ S ∧ c - v ∈ (convexHull ℝ (S : Set E)).extremePoints ℝ := by
  obtain ⟨s', hs', hsum⟩ := hconv g v h
  have : s' = c - v := by rw [← hsum]; abel
  subst this
  exact ⟨hs'.1, prop2_unique hs'⟩

end BallotPolytope

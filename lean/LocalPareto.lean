/-
  The stages of the symmetry problem for local Pareto rules, three
  alternatives (`notes/equivariant-obstructions.md`, Sections 1–3).

  A rule F sends profiles of positions on the hexagon (as in `GlobalForm.lean`)
  to positions. It is **local** (`Local`) if a step of one voter moves the
  social ranking by at most one step, and **Pareto** (`Pareto`) if it respects
  every comparison on which all voters agree. Every IIA rule is local, and
  every unanimous IIA rule is Pareto; neither condition implies IIA.

  Method. Locality makes every small square (a step of one voter and a step
  of another) a closed walk of four adjacent moves, which winds 0
  (`square`). Summing small squares gives the invariance of the degree
  (`W_indep_loc`), as Lemma 1 of *The Global Form*, without IIA. For the sum
  of the degrees the voters walk a staircase (`stair`): one step each, in a
  fixed order, then the next. Along it every profile has all voters on one
  edge of the hexagon, so Pareto keeps the social ranking on that edge and
  the staircase winds once (`Wst_pareto`). Small squares again split the
  staircase into the voters' loops (`Wst_eq`, through the torus identity
  `torus`).

  Results:
  * `W_indep_loc` (Section 1): for a local rule the degree does not depend on
    the context;
  * `W_sum_pareto` (Section 1): for a local Pareto rule the windings of the
    voters sum to one turn, so the degrees sum to 1 (`deg_sum`);
  * `pinning` (Lemma 2): every degree is 0 or 1 (`deg_cases`);
  * `deg_perm` (the first part of the proof of Proposition 1): a symmetry
    (σ, γ), a permutation of the voters with a symmetry of the hexagon, gives
    voter σ i the degree of voter i;
  * `prop1` (Proposition 1): the degrees are constant on the orbits of the
    group P of voter permutations, sum to 1, and so every common divisor of
    the orbit sizes is 1;
  * `prop3` (Proposition 3): a local Pareto rule symmetric under a set K of
    symmetries exists exactly when the voter permutations of K fix a common
    voter;
  * `prop6_iia`, `prop6_anonymous` (Proposition 6 of *The Global Form*, for IIA
    rules into rankings): every IIA rule is local (`local_of_iia`), so the
    symmetries of the hexagon act on the degrees only through the voters they
    permute, and a unanimous anonymous IIA rule exists only for one voter.

  The symmetries of the hexagon are written as the twelve maps k ↦ t + k and
  k ↦ t − k (`hact`). The renamings of the alternatives and reversal act on
  the hexagon as these twelve maps (Section 1 of the note); that
  identification is not checked here. The arithmetic converse of
  Proposition 1 (integer vectors exist when the gcd is 1) and the stages 0
  and 1 are not formalised.
-/

module

public import Mathlib
public import GlobalForm

@[expose] public section

open Finset
open GlobalForm (Adj bit delta wind setS setS_self W deg)

namespace LocalPareto

/-! ### The hexagon -/

lemma delta_bound : ∀ a b : Fin 6, -1 ≤ delta a b ∧ delta a b ≤ 1 := by decide

lemma adj_lift : ∀ a b : Fin 6, (b = a ∨ b = a + 1 ∨ a = b + 1) →
    ((b.val : ℤ) - a.val - delta a b) % 6 = 0 := by decide

lemma square_fin : ∀ x y z w : Fin 6, (y = x ∨ y = x + 1 ∨ x = y + 1) →
    (w = y ∨ w = y + 1 ∨ y = w + 1) → (z = x ∨ z = x + 1 ∨ x = z + 1) →
    (w = z ∨ w = z + 1 ∨ z = w + 1) → delta x y + delta y w = delta x z + delta z w := by
  decide

/-- **Small squares.** A closed walk of four adjacent moves winds 0. -/
lemma square {x y z w : Fin 6} (h1 : Adj x y) (h2 : Adj y w) (h3 : Adj x z) (h4 : Adj z w) :
    delta x y + delta y w = delta x z + delta z w :=
  square_fin x y z w h1 h2 h3 h4

lemma wind_sum (w : Fin 6 → Fin 6) : wind w = ∑ k, delta (w k) (w (k + 1)) := by
  rw [Fin.sum_univ_six]
  rfl

/-- Two walks joined by adjacent rungs, with small squares between them, wind
    alike. -/
lemma grid_row (A B : Fin 6 → Fin 6)
    (h : ∀ k, delta (A k) (A (k + 1)) + delta (A (k + 1)) (B (k + 1)) =
      delta (A k) (B k) + delta (B k) (B (k + 1))) : wind A = wind B := by
  rw [wind_sum, wind_sum]
  have hs : ∑ k, (delta (A k) (A (k + 1)) + delta (A (k + 1)) (B (k + 1))) =
      ∑ k, (delta (A k) (B k) + delta (B k) (B (k + 1))) := sum_congr rfl fun k _ => h k
  rw [sum_add_distrib, sum_add_distrib] at hs
  have shift : ∑ k : Fin 6, delta (A (k + 1)) (B (k + 1)) = ∑ k, delta (A k) (B k) :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin 6)) (fun k => delta (A k) (B k))
  linarith

lemma pin_arith (v0 v1 v2 v3 v4 v5 d0 d1 d2 d3 d4 d5 : ℤ)
    (l0 : (v1 - v0 - d0) % 6 = 0) (l1 : (v2 - v1 - d1) % 6 = 0) (l2 : (v3 - v2 - d2) % 6 = 0)
    (l3 : (v4 - v3 - d3) % 6 = 0) (l4 : (v5 - v4 - d4) % 6 = 0) (l5 : (v0 - v5 - d5) % 6 = 0)
    (b0 : -1 ≤ d0 ∧ d0 ≤ 1) (b1 : -1 ≤ d1 ∧ d1 ≤ 1) (b2 : -1 ≤ d2 ∧ d2 ≤ 1)
    (b3 : -1 ≤ d3 ∧ d3 ≤ 1) (b4 : -1 ≤ d4 ∧ d4 ≤ 1) (b5 : -1 ≤ d5 ∧ d5 ≤ 1) (h0 : 0 ≤ d0) :
    d0 + d1 + d2 + d3 + d4 + d5 = 0 ∨ d0 + d1 + d2 + d3 + d4 + d5 = 6 := by
  omega

/-- A closed walk of six adjacent moves whose first move does not go back
    winds 0 or once. -/
lemma wind_pin (w : Fin 6 → Fin 6) (h : ∀ k, Adj (w k) (w (k + 1)))
    (h0 : 0 ≤ delta (w 0) (w 1)) : wind w = 0 ∨ wind w = 6 := by
  have a0 : Adj (w 0) (w 1) := h 0
  have a1 : Adj (w 1) (w 2) := h 1
  have a2 : Adj (w 2) (w 3) := h 2
  have a3 : Adj (w 3) (w 4) := h 3
  have a4 : Adj (w 4) (w 5) := h 4
  have a5 : Adj (w 5) (w 0) := h 5
  have l0 := adj_lift _ _ a0
  have l1 := adj_lift _ _ a1
  have l2 := adj_lift _ _ a2
  have l3 := adj_lift _ _ a3
  have l4 := adj_lift _ _ a4
  have l5 := adj_lift _ _ a5
  have b0 := delta_bound (w 0) (w 1)
  have b1 := delta_bound (w 1) (w 2)
  have b2 := delta_bound (w 2) (w 3)
  have b3 := delta_bound (w 3) (w 4)
  have b4 := delta_bound (w 4) (w 5)
  have b5 := delta_bound (w 5) (w 0)
  unfold wind
  exact pin_arith _ _ _ _ _ _ _ _ _ _ _ _ l0 l1 l2 l3 l4 l5 b0 b1 b2 b3 b4 b5 h0

/-- **The torus identity.** On the 6 × 6 grid, if every small square commutes,
    the diagonal loop is the sum of a row and a column. -/
lemma torus (G D : Fin 6 → Fin 6 → ℤ) (h : ∀ a b, G a b + D (a + 1) b = D a b + G a (b + 1)) :
    ∑ a, (G a a + D (a + 1) a) = ∑ a, G a 0 + ∑ b, D 0 b := by
  rw [Fin.sum_univ_six, Fin.sum_univ_six, Fin.sum_univ_six]
  have h00 : G 0 0 + D 1 0 = D 0 0 + G 0 1 := h 0 0
  have h01 : G 0 1 + D 1 1 = D 0 1 + G 0 2 := h 0 1
  have h02 : G 0 2 + D 1 2 = D 0 2 + G 0 3 := h 0 2
  have h03 : G 0 3 + D 1 3 = D 0 3 + G 0 4 := h 0 3
  have h04 : G 0 4 + D 1 4 = D 0 4 + G 0 5 := h 0 4
  have h05 : G 0 5 + D 1 5 = D 0 5 + G 0 0 := h 0 5
  have h10 : G 1 0 + D 2 0 = D 1 0 + G 1 1 := h 1 0
  have h11 : G 1 1 + D 2 1 = D 1 1 + G 1 2 := h 1 1
  have h12 : G 1 2 + D 2 2 = D 1 2 + G 1 3 := h 1 2
  have h13 : G 1 3 + D 2 3 = D 1 3 + G 1 4 := h 1 3
  have h14 : G 1 4 + D 2 4 = D 1 4 + G 1 5 := h 1 4
  have h15 : G 1 5 + D 2 5 = D 1 5 + G 1 0 := h 1 5
  have h20 : G 2 0 + D 3 0 = D 2 0 + G 2 1 := h 2 0
  have h21 : G 2 1 + D 3 1 = D 2 1 + G 2 2 := h 2 1
  have h22 : G 2 2 + D 3 2 = D 2 2 + G 2 3 := h 2 2
  have h23 : G 2 3 + D 3 3 = D 2 3 + G 2 4 := h 2 3
  have h24 : G 2 4 + D 3 4 = D 2 4 + G 2 5 := h 2 4
  have h25 : G 2 5 + D 3 5 = D 2 5 + G 2 0 := h 2 5
  have h30 : G 3 0 + D 4 0 = D 3 0 + G 3 1 := h 3 0
  have h31 : G 3 1 + D 4 1 = D 3 1 + G 3 2 := h 3 1
  have h32 : G 3 2 + D 4 2 = D 3 2 + G 3 3 := h 3 2
  have h33 : G 3 3 + D 4 3 = D 3 3 + G 3 4 := h 3 3
  have h34 : G 3 4 + D 4 4 = D 3 4 + G 3 5 := h 3 4
  have h35 : G 3 5 + D 4 5 = D 3 5 + G 3 0 := h 3 5
  have h40 : G 4 0 + D 5 0 = D 4 0 + G 4 1 := h 4 0
  have h41 : G 4 1 + D 5 1 = D 4 1 + G 4 2 := h 4 1
  have h42 : G 4 2 + D 5 2 = D 4 2 + G 4 3 := h 4 2
  have h43 : G 4 3 + D 5 3 = D 4 3 + G 4 4 := h 4 3
  have h44 : G 4 4 + D 5 4 = D 4 4 + G 4 5 := h 4 4
  have h45 : G 4 5 + D 5 5 = D 4 5 + G 4 0 := h 4 5
  have h50 : G 5 0 + D 0 0 = D 5 0 + G 5 1 := h 5 0
  have h51 : G 5 1 + D 0 1 = D 5 1 + G 5 2 := h 5 1
  have h52 : G 5 2 + D 0 2 = D 5 2 + G 5 3 := h 5 2
  have h53 : G 5 3 + D 0 3 = D 5 3 + G 5 4 := h 5 3
  have h54 : G 5 4 + D 0 4 = D 5 4 + G 5 5 := h 5 4
  have h55 : G 5 5 + D 0 5 = D 5 5 + G 5 0 := h 5 5
  show (G 0 0 + D 1 0) + (G 1 1 + D 2 1) + (G 2 2 + D 3 2) + (G 3 3 + D 4 3) + (G 4 4 + D 5 4) + (G 5 5 + D 0 5) =
    (G 0 0 + G 1 0 + G 2 0 + G 3 0 + G 4 0 + G 5 0) + (D 0 0 + D 0 1 + D 0 2 + D 0 3 + D 0 4 + D 0 5)
  linarith

/-- The two rankings on the edge from a to a + 1 are the only ones that agree
    with a on the two comparisons the edge leaves alone. -/
lemma edge_fin : ∀ a x : Fin 6, (∀ e : Fin 3, bit e a = bit e (a + 1) → bit e x = bit e a) →
    x = a ∨ x = a + 1 := by decide

lemma vertex_fin : ∀ a x : Fin 6, (∀ e : Fin 3, bit e x = bit e a) → x = a := by decide

/-- On an edge the steps telescope. -/
def ind (a z : Fin 6) : ℤ := if z = a + 1 then 1 else 0

lemma edge_delta : ∀ a x y : Fin 6, (x = a ∨ x = a + 1) → (y = a ∨ y = a + 1) →
    delta x y = ind a y - ind a x := by decide

lemma ind_self : ∀ a : Fin 6, ind a a = 0 := by decide

lemma ind_succ : ∀ a : Fin 6, ind a (a + 1) = 1 := by decide

/-! ### Local and Pareto rules -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A step of one voter moves the social ranking by at most one step. -/
def Local (F : (ι → Fin 6) → Fin 6) : Prop :=
  ∀ (π : ι → Fin 6) (i : ι), Adj (F π) (F (Function.update π i (π i + 1)))

/-- The social ranking respects every comparison on which all voters agree. -/
def Pareto (F : (ι → Fin 6) → Fin 6) : Prop :=
  ∀ (π : ι → Fin 6) (e : Fin 3) (b : Bool), (∀ i, bit e (π i) = b) → bit e (F π) = b

variable {F : (ι → Fin 6) → Fin 6}

omit [Fintype ι] [DecidableEq ι] in
lemma pareto_edge (hP : Pareto F) (a : Fin 6) (π : ι → Fin 6)
    (h : ∀ v, π v = a ∨ π v = a + 1) : F π = a ∨ F π = a + 1 := by
  apply edge_fin
  intro e he
  apply hP π e
  intro v
  rcases h v with h' | h' <;> rw [h']
  exact he.symm

omit [Fintype ι] [DecidableEq ι] in
lemma pareto_unan (hP : Pareto F) (a : Fin 6) (π : ι → Fin 6) (h : ∀ v, π v = a) :
    F π = a :=
  vertex_fin a _ fun e => hP π e _ fun v => by rw [h]

omit [Fintype ι] in
lemma setS_succ (i : ι) (k : Fin 6) (c : ι → Fin 6) :
    setS {i} (k + 1) c = Function.update (setS {i} k c) i (setS {i} k c i + 1) := by
  funext v
  by_cases h : v = i
  · subst h
    simp [setS]
  · simp [setS, h]

omit [Fintype ι] in
lemma setS_other {i j : ι} (hij : i ≠ j) (k q : Fin 6) (c : ι → Fin 6) :
    setS {i} k (setS {j} (q + 1) c) =
      Function.update (setS {i} k (setS {j} q c)) j (setS {i} k (setS {j} q c) j + 1) := by
  funext v
  by_cases hv : v = j
  · subst hv
    simp [setS, Ne.symm hij]
  · by_cases hvi : v = i
    · subst hvi
      simp [setS, hv]
    · simp [setS, hv, hvi]

omit [Fintype ι] in
lemma adj_walk (hF : Local F) (i : ι) (k : Fin 6) (c : ι → Fin 6) :
    Adj (F (setS {i} k c)) (F (setS {i} (k + 1) c)) := by
  rw [setS_succ]
  exact hF _ _

/-! ### Lemma 1 without IIA: invariance -/

omit [Fintype ι] in
lemma W_step (hF : Local F) {i j : ι} (hij : i ≠ j) (q : Fin 6) (c : ι → Fin 6) :
    W F {i} (setS {j} q c) = W F {i} (setS {j} (q + 1) c) := by
  unfold W
  apply grid_row
  intro k
  apply square
  · exact adj_walk hF i k _
  · rw [setS_other hij]
    exact hF _ _
  · rw [setS_other hij]
    exact hF _ _
  · exact adj_walk hF i k _

omit [Fintype ι] in
lemma W_upd_loc (hF : Local F) (i j : ι) (c : ι → Fin 6) (p : Fin 6) :
    W F {i} (setS {j} p c) = W F {i} c := by
  by_cases hij : i = j
  · subst hij
    unfold W
    congr 1
    funext k
    congr 1
    funext v
    by_cases hv : v = i <;> simp [setS, hv]
  · have s0 : W F {i} (setS {j} 0 c) = W F {i} (setS {j} 1 c) := W_step hF hij 0 c
    have s1 : W F {i} (setS {j} 1 c) = W F {i} (setS {j} 2 c) := W_step hF hij 1 c
    have s2 : W F {i} (setS {j} 2 c) = W F {i} (setS {j} 3 c) := W_step hF hij 2 c
    have s3 : W F {i} (setS {j} 3 c) = W F {i} (setS {j} 4 c) := W_step hF hij 3 c
    have s4 : W F {i} (setS {j} 4 c) = W F {i} (setS {j} 5 c) := W_step hF hij 4 c
    have h0 : ∀ q : Fin 6, W F {i} (setS {j} q c) = W F {i} (setS {j} 0 c) := by
      intro q
      fin_cases q
      exacts [rfl, s0.symm, (s0.trans s1).symm, (s0.trans (s1.trans s2)).symm,
        (s0.trans (s1.trans (s2.trans s3))).symm,
        (s0.trans (s1.trans (s2.trans (s3.trans s4)))).symm]
    have hc := h0 (c j)
    rw [setS_self] at hc
    rw [h0 p, hc]

/-- **Invariance.** For a local rule a voter's winding does not depend on
    where the other voters stand. -/
theorem W_indep_loc (hF : Local F) (i : ι) (c c' : ι → Fin 6) : W F {i} c = W F {i} c' := by
  have key : ∀ U : Finset ι, W F {i} c = W F {i} (fun v => if v ∈ U then c' v else c v) := by
    intro U
    induction U using Finset.induction_on with
    | empty => simp
    | @insert j U _ ih =>
      rw [ih]
      have : (fun v => if v ∈ insert j U then c' v else c v) =
          setS {j} (c' j) (fun v => if v ∈ U then c' v else c v) := by
        funext v
        unfold setS
        by_cases hvj : v = j
        · subst hvj
          simp
        · simp [hvj]
      rw [this, W_upd_loc hF]
  simpa using key univ

/-! ### The staircase -/

/-- The staircase profile: of the first M voters in the order e, those before
    m stand at a + 1 and the others at a; the voters from M on stand as in c. -/
def stair {n : ℕ} (e : ι ≃ Fin n) (M : ℕ) (a : Fin 6) (m : ℕ) (c : ι → Fin 6) : ι → Fin 6 :=
  fun v => if (e v : ℕ) < m then a + 1 else if (e v : ℕ) < M then a else c v

/-- The social steps while the first M voters move from a to a + 1, one by one. -/
def bstep (F : (ι → Fin 6) → Fin 6) {n : ℕ} (e : ι ≃ Fin n) (M : ℕ) (a : Fin 6)
    (c : ι → Fin 6) : ℤ :=
  ∑ m ∈ range M, delta (F (stair e M a m c)) (F (stair e M a (m + 1) c))

/-- The winding of the staircase of the first M voters around the hexagon. -/
def Wst (F : (ι → Fin 6) → Fin 6) {n : ℕ} (e : ι ≃ Fin n) (M : ℕ) (c : ι → Fin 6) : ℤ :=
  ∑ a : Fin 6, bstep F e M a c

section stair

variable {n : ℕ} (e : ι ≃ Fin n)

omit [Fintype ι] in
lemma stair_succ {M m : ℕ} (hm : m < M) {u : ι} (hu : (e u : ℕ) = m) (a : Fin 6)
    (c : ι → Fin 6) :
    stair e M a (m + 1) c = Function.update (stair e M a m c) u (stair e M a m c u + 1) := by
  funext v
  by_cases hv : v = u
  · subst hv
    simp [stair, hu, hm]
  · have hne : (e v : ℕ) ≠ m := fun h => hv (e.injective (Fin.ext (h.trans hu.symm)))
    rw [Function.update_of_ne hv]
    unfold stair
    by_cases h1 : (e v : ℕ) < m
    · simp [h1, show (e v : ℕ) < m + 1 by omega]
    · simp [h1, show ¬ (e v : ℕ) < m + 1 by omega]

omit [Fintype ι] in
lemma stair_other {M m : ℕ} (hm : m ≤ M) {j : ι} (hj : (e j : ℕ) = M) (a b : Fin 6)
    (c : ι → Fin 6) :
    stair e M a m (setS {j} (b + 1) c) = Function.update (stair e M a m (setS {j} b c)) j
      (stair e M a m (setS {j} b c) j + 1) := by
  funext v
  by_cases hv : v = j
  · subst hv
    simp [stair, setS, hj, show ¬ M < m by omega]
  · rw [Function.update_of_ne hv]
    unfold stair setS
    simp [hv]

omit [Fintype ι] in
lemma stair_lift {M m : ℕ} (hm : m ≤ M) {j : ι} (hj : (e j : ℕ) = M) (a : Fin 6)
    (c : ι → Fin 6) : stair e (M + 1) a m c = stair e M a m (setS {j} a c) := by
  funext v
  by_cases hv : v = j
  · subst hv
    simp [stair, setS, hj, show ¬ M < m by omega]
  · have hne : (e v : ℕ) ≠ M := fun h => hv (e.injective (Fin.ext (h.trans hj.symm)))
    unfold stair setS
    by_cases h1 : (e v : ℕ) < m
    · simp [h1]
    · by_cases h2 : (e v : ℕ) < M
      · simp [h1, h2, show (e v : ℕ) < M + 1 by omega]
      · simp [h1, h2, hv, show ¬ (e v : ℕ) < M + 1 by omega]

omit [Fintype ι] [DecidableEq ι] in
lemma stair_top (M : ℕ) (a : Fin 6) (c : ι → Fin 6) :
    stair e M a M c = stair e M (a + 1) 0 c := by
  funext v
  unfold stair
  by_cases h : (e v : ℕ) < M <;> simp [h]

omit [Fintype ι] in
lemma stair_full {M : ℕ} {j : ι} (hj : (e j : ℕ) = M) (a : Fin 6) (c : ι → Fin 6) :
    stair e (M + 1) a (M + 1) c = stair e M (a + 1) 0 (setS {j} (a + 1) c) := by
  funext v
  by_cases hv : v = j
  · subst hv
    simp [stair, setS, hj]
  · have hne : (e v : ℕ) ≠ M := fun h => hv (e.injective (Fin.ext (h.trans hj.symm)))
    unfold stair setS
    by_cases h2 : (e v : ℕ) < M
    · simp [h2, show (e v : ℕ) < M + 1 by omega]
    · simp [h2, hv, show ¬ (e v : ℕ) < M + 1 by omega]

omit [Fintype ι] in
lemma stair_base {M : ℕ} {j : ι} (hj : (e j : ℕ) = M) (b : Fin 6) (c : ι → Fin 6) :
    stair e M 0 0 (setS {j} b c) = setS {j} b (stair e M 0 0 c) := by
  funext v
  by_cases hv : v = j
  · subst hv
    simp [stair, setS, hj]
  · unfold stair setS
    simp [hv]

omit [Fintype ι] in
/-- **Small squares along a staircase step.** The first M voters' step from a
    to a + 1 commutes with a step of voter j, as a sum of small squares. -/
lemma bstep_square (hF : Local F) {M : ℕ} (hMn : M < n) {j : ι} (hj : (e j : ℕ) = M)
    (a b : Fin 6) (c : ι → Fin 6) :
    bstep F e M a (setS {j} b c) +
        delta (F (stair e M (a + 1) 0 (setS {j} b c)))
          (F (stair e M (a + 1) 0 (setS {j} (b + 1) c))) =
      delta (F (stair e M a 0 (setS {j} b c))) (F (stair e M a 0 (setS {j} (b + 1) c))) +
        bstep F e M a (setS {j} (b + 1) c) := by
  set X : ℕ → Fin 6 := fun m => F (stair e M a m (setS {j} b c)) with hX
  set Y : ℕ → Fin 6 := fun m => F (stair e M a m (setS {j} (b + 1) c)) with hY
  have sq : ∀ m ∈ range M, delta (X m) (X (m + 1)) + delta (X (m + 1)) (Y (m + 1)) =
      delta (X m) (Y m) + delta (Y m) (Y (m + 1)) := by
    intro m hm
    rw [mem_range] at hm
    have hmn : m < n := by omega
    have hu : ((e (e.symm ⟨m, hmn⟩)) : ℕ) = m := by simp
    apply square
    · simp only [hX]
      rw [stair_succ e hm hu]
      exact hF _ _
    · simp only [hX, hY]
      rw [stair_other e (m := m + 1) (by omega) hj]
      exact hF _ _
    · simp only [hX, hY]
      rw [stair_other e (m := m) (by omega) hj]
      exact hF _ _
    · simp only [hY]
      rw [stair_succ e hm hu]
      exact hF _ _
  have hs := sum_congr rfl sq
  rw [sum_add_distrib, sum_add_distrib] at hs
  have tel : ∑ m ∈ range M, (delta (X (m + 1)) (Y (m + 1)) - delta (X m) (Y m)) =
      delta (X M) (Y M) - delta (X 0) (Y 0) := Finset.sum_range_sub (fun m => delta (X m) (Y m)) M
  rw [sum_sub_distrib] at tel
  have top : delta (X M) (Y M) = delta (F (stair e M (a + 1) 0 (setS {j} b c)))
      (F (stair e M (a + 1) 0 (setS {j} (b + 1) c))) := by
    simp only [hX, hY, stair_top]
  unfold bstep
  rw [← top]
  change ∑ m ∈ range M, delta (X m) (X (m + 1)) + delta (X M) (Y M) =
    delta (X 0) (Y 0) + ∑ m ∈ range M, delta (Y m) (Y (m + 1))
  linarith

end stair

/-- **The staircase splits into the voters' loops.** For a local rule, the
    staircase of the first M voters winds as much as their loops together. -/
theorem Wst_eq (hF : Local F) {n : ℕ} (e : ι ≃ Fin n) :
    ∀ M ≤ n, ∀ c : ι → Fin 6,
      Wst F e M c = ∑ v ∈ univ.filter (fun v => (e v : ℕ) < M), W F {v} c := by
  intro M
  induction M with
  | zero =>
    intro _ c
    simp [Wst, bstep]
  | succ M ih =>
    intro hM c
    have hMn : M < n := by omega
    set j := e.symm ⟨M, hMn⟩ with hjdef
    have hj : (e j : ℕ) = M := by simp [hjdef]
    -- the grid of the first M voters (rows) and voter j (columns)
    set G : Fin 6 → Fin 6 → ℤ := fun a b => bstep F e M a (setS {j} b c) with hG
    set D : Fin 6 → Fin 6 → ℤ := fun a b =>
      delta (F (stair e M a 0 (setS {j} b c))) (F (stair e M a 0 (setS {j} (b + 1) c))) with hD
    have hsq : ∀ a b, G a b + D (a + 1) b = D a b + G a (b + 1) := fun a b =>
      bstep_square e hF hMn hj a b c
    have hdiag : ∀ a, bstep F e (M + 1) a c = G a a + D (a + 1) a := by
      intro a
      show _ = bstep F e M a (setS {j} a c) + delta (F (stair e M (a + 1) 0 (setS {j} a c)))
        (F (stair e M (a + 1) 0 (setS {j} (a + 1) c)))
      unfold bstep
      rw [sum_range_succ]
      congr 1
      · refine sum_congr rfl fun m hm => ?_
        rw [mem_range] at hm
        rw [stair_lift e (m := m) (by omega) hj, stair_lift e (m := m + 1) (by omega) hj]
      · rw [stair_lift e le_rfl hj, stair_top, stair_full e hj]
    have hrow : ∑ a, G a 0 = Wst F e M (setS {j} 0 c) := rfl
    have hcol : ∑ b, D 0 b = W F {j} (stair e M 0 0 c) := by
      simp only [hD, stair_base e hj]
      unfold W
      rw [wind_sum]
    have hW : Wst F e (M + 1) c = Wst F e M (setS {j} 0 c) + W F {j} (stair e M 0 0 c) := by
      rw [show Wst F e (M + 1) c = ∑ a, (G a a + D (a + 1) a) from sum_congr rfl fun a _ => hdiag a,
        torus G D hsq, hrow, hcol]
    have hfil : univ.filter (fun v => (e v : ℕ) < M + 1) =
        insert j (univ.filter fun v => (e v : ℕ) < M) := by
      ext v
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · intro h
        by_cases h' : (e v : ℕ) < M
        · exact Or.inr h'
        · left
          exact e.injective (Fin.ext (by rw [hj]; omega))
      · rintro (h | h)
        · rw [h, hj]
          omega
        · omega
    have hjn : j ∉ univ.filter fun v => (e v : ℕ) < M := by
      simp [hj]
    rw [hW, ih (by omega), hfil, sum_insert hjn, W_indep_loc hF j (stair e M 0 0 c) c,
      sum_congr rfl fun v _ => W_indep_loc hF v (setS {j} 0 c) c]
    ring

omit [Fintype ι] [DecidableEq ι] in
/-- **With Pareto the staircase winds once.** Along each of its steps all voters
    stand on one edge of the hexagon. -/
theorem Wst_pareto (hP : Pareto F) {n : ℕ} (e : ι ≃ Fin n) (c : ι → Fin 6) :
    Wst F e n c = 6 := by
  have hstep : ∀ a, bstep F e n a c = 1 := by
    intro a
    have hon : ∀ m, F (stair e n a m c) = a ∨ F (stair e n a m c) = a + 1 := fun m =>
      pareto_edge hP a _ fun v => by
        unfold stair
        by_cases h : (e v : ℕ) < m
        · simp [h]
        · simp [h, (e v).isLt]
    have tel : ∑ m ∈ range n, (ind a (F (stair e n a (m + 1) c)) - ind a (F (stair e n a m c))) =
        ind a (F (stair e n a n c)) - ind a (F (stair e n a 0 c)) :=
      sum_range_sub (fun m => ind a (F (stair e n a m c))) n
    unfold bstep
    rw [sum_congr rfl fun m _ => edge_delta a _ _ (hon m) (hon (m + 1)), tel]
    have h0 : F (stair e n a 0 c) = a :=
      pareto_unan hP a _ fun v => by simp [stair, (e v).isLt]
    have hn : F (stair e n a n c) = a + 1 :=
      pareto_unan hP (a + 1) _ fun v => by simp [stair, (e v).isLt]
    simp only [h0, hn, ind_self, ind_succ]
    norm_num
  unfold Wst
  simp [hstep]

/-- **The sum (Section 1).** For a local Pareto rule the voters' windings sum
    to one turn. -/
theorem W_sum_pareto (hF : Local F) (hP : Pareto F) (c : ι → Fin 6) :
    ∑ v, W F {v} c = 6 := by
  have h := Wst_eq hF (Fintype.equivFin ι) _ le_rfl c
  rw [Wst_pareto hP, filter_true_of_mem fun v _ => ((Fintype.equivFin ι) v).isLt] at h
  exact h.symm

/-- **Lemma 2 (pinning).** Every degree of a local Pareto rule is 0 or 1: with
    the others at abc, the first step of a voter's walk goes forward or stands
    still. -/
theorem pinning (hF : Local F) (hP : Pareto F) (i : ι) (c : ι → Fin 6) :
    W F {i} c = 0 ∨ W F {i} c = 6 := by
  rw [W_indep_loc hF i c (fun _ => 0)]
  apply wind_pin
  · exact fun k => adj_walk hF i k _
  · have w0 : F (setS {i} 0 (fun _ => 0)) = 0 :=
      pareto_unan hP 0 _ fun v => by unfold setS; split_ifs <;> rfl
    have w1 : F (setS {i} 1 (fun _ => 0)) = 0 ∨ F (setS {i} 1 (fun _ => 0)) = 0 + 1 :=
      pareto_edge hP 0 _ fun v => by unfold setS; split_ifs <;> simp
    show 0 ≤ delta (F (setS {i} 0 (fun _ => 0))) (F (setS {i} 1 (fun _ => 0)))
    rw [w0]
    rcases w1 with h | h <;> rw [h] <;> decide

theorem deg_cases (hF : Local F) (hP : Pareto F) (i : ι) (c : ι → Fin 6) :
    (deg F i c = 0 ∧ W F {i} c = 0) ∨ (deg F i c = 1 ∧ W F {i} c = 6) := by
  unfold deg
  rcases pinning hF hP i c with h | h <;> rw [h] <;> norm_num

/-- With Pareto the degrees sum to 1. -/
theorem deg_sum (hF : Local F) (hP : Pareto F) (c : ι → Fin 6) : ∑ i, deg F i c = 1 := by
  have h6 : ∀ i, W F {i} c = 6 * deg F i c := fun i => by
    rcases deg_cases hF hP i c with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> norm_num
  have := W_sum_pareto hF hP c
  rw [sum_congr rfl fun i _ => h6 i, ← mul_sum] at this
  omega

/-! ### Symmetries -/

/-- The twelve symmetries of the hexagon: the rotations k ↦ t + k (`false`) and
    the reflections k ↦ t − k (`true`). -/
def hact : Bool → Fin 6 → Fin 6 → Fin 6
  | false, t, k => t + k
  | true, t, k => t - k

def hinv : Bool → Fin 6 → Fin 6 → Fin 6
  | false, t, k => k - t
  | true, t, k => t - k

lemma hact_hinv : ∀ (s : Bool) (t k : Fin 6), hact s t (hinv s t k) = k := by decide

lemma delta_rot : ∀ t x y : Fin 6, delta (t + x) (t + y) = delta x y := by decide

lemma delta_refl : ∀ t x y : Fin 6, delta (t - x) (t - y) = delta y x := by decide

lemma fin_rot : ∀ k t : Fin 6, k + 1 - t = k - t + 1 := by decide

lemma fin_refl1 : ∀ k t : Fin 6, t - k - 1 + 1 = t - k := by decide

lemma fin_refl2 : ∀ k t : Fin 6, t - (k + 1) = t - k - 1 := by decide

/-- F commutes with the symmetry that permutes the voters by σ and moves
    every ballot and the outcome by the hexagon symmetry `hact s t`. -/
def Equivariant (F : (ι → Fin 6) → Fin 6) (σ : Equiv.Perm ι) (s : Bool) (t : Fin 6) : Prop :=
  ∀ π : ι → Fin 6, F (fun v => hact s t (π (σ.symm v))) = hact s t (F π)

omit [Fintype ι] in
/-- A symmetry moves voter i's loop to voter σ i's loop. The hexagon symmetry
    acts with the same sign on the ballots and on the outcome, so the winding
    is kept. -/
theorem W_perm {σ : Equiv.Perm ι} {s : Bool} {t : Fin 6} (hE : Equivariant F σ s t) (i : ι)
    (c : ι → Fin 6) : W F {σ i} c = W F {i} (fun v => hinv s t (c (σ v))) := by
  set c' : ι → Fin 6 := fun v => hinv s t (c (σ v)) with hc'
  have key : ∀ k, F (setS {σ i} k c) = hact s t (F (setS {i} (hinv s t k) c')) := by
    intro k
    rw [← hE]
    congr 1
    funext v
    by_cases hv : v = σ i
    · subst hv
      simp [setS, hact_hinv]
    · have hv' : σ.symm v ≠ i := fun h => hv (by rw [← h]; simp)
      simp [setS, hv, hv', hc', hact_hinv]
  unfold W
  rw [wind_sum, wind_sum]
  simp only [key]
  cases s
  · refine (sum_congr rfl fun k _ => ?_).trans (Equiv.sum_comp (Equiv.subRight t)
      (fun m => delta (F (setS {i} m c')) (F (setS {i} (m + 1) c'))))
    simp only [hact, hinv, delta_rot, Equiv.subRight_apply]
    rw [fin_rot k t]
  · refine (sum_congr rfl fun k _ => ?_).trans (Equiv.sum_comp
      ((Equiv.subLeft t).trans (Equiv.subRight 1))
      (fun m => delta (F (setS {i} m c')) (F (setS {i} (m + 1) c'))))
    simp only [hact, hinv, delta_refl, Equiv.trans_apply, Equiv.subLeft_apply,
      Equiv.subRight_apply]
    rw [fin_refl1 k t, fin_refl2 k t]

/-- **Degrees are constant along symmetries** (the first part of the proof of
    Proposition 1). -/
theorem deg_perm (hF : Local F) {σ : Equiv.Perm ι} {s : Bool} {t : Fin 6}
    (hE : Equivariant F σ s t) (i : ι) (c : ι → Fin 6) : deg F (σ i) c = deg F i c := by
  unfold deg
  rw [W_perm hE, W_indep_loc hF i (fun v => hinv s t (c (σ v))) c]

/-! ### Orbits -/

/-- The orbits of a group P of voter permutations. -/
def orbSetoid (P : Subgroup (Equiv.Perm ι)) : Setoid ι where
  r i j := ∃ σ ∈ P, σ i = j
  iseqv := ⟨fun _ => ⟨1, P.one_mem, rfl⟩,
    fun ⟨σ, hσ, h⟩ => ⟨σ⁻¹, P.inv_mem hσ, by rw [← h]; simp⟩,
    fun ⟨σ, hσ, h⟩ ⟨τ, hτ, h'⟩ => ⟨τ * σ, P.mul_mem hτ hσ, by rw [Equiv.Perm.mul_apply, h, h']⟩⟩

/-- The size of the orbit of voter i under P. -/
noncomputable def orbSize (P : Subgroup (Equiv.Perm ι)) (i : ι) : ℕ :=
  Nat.card {j // ∃ σ ∈ P, σ i = j}

omit [DecidableEq ι] in
/-- A function constant on orbits sums to a multiple of every common divisor of
    the orbit sizes. -/
theorem dvd_sum_orbits (P : Subgroup (Equiv.Perm ι)) (d : ι → ℤ)
    (hd : ∀ σ ∈ P, ∀ i, d (σ i) = d i) (g : ℕ) (hg : ∀ i, g ∣ orbSize P i) :
    (g : ℤ) ∣ ∑ i, d i := by
  classical
  rw [← Finset.sum_fiberwise univ (fun i => Quotient.mk (orbSetoid P) i) d]
  apply Finset.dvd_sum
  intro q _
  obtain ⟨i0, rfl⟩ := Quotient.exists_rep q
  have hconst : ∀ i ∈ univ.filter (fun i => Quotient.mk (orbSetoid P) i =
      Quotient.mk (orbSetoid P) i0), d i = d i0 := by
    intro i hi
    rw [mem_filter] at hi
    obtain ⟨σ, hσ, h⟩ := Quotient.exact hi.2
    rw [← h, hd σ hσ]
  have hcard : (univ.filter fun i => Quotient.mk (orbSetoid P) i =
      Quotient.mk (orbSetoid P) i0) = univ.filter fun j => ∃ σ ∈ P, σ i0 = j := by
    apply filter_congr
    intro j _
    constructor
    · intro h
      exact Quotient.exact h.symm
    · intro h
      exact (Quotient.sound (s := orbSetoid P) (a := i0) (b := j) h).symm
  have hsize : orbSize P i0 = (univ.filter fun j => ∃ σ ∈ P, σ i0 = j).card := by
    rw [orbSize, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [sum_congr rfl hconst, sum_const, nsmul_eq_mul, hcard, ← hsize]
  exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr (hg i0)) _

/-! ### Propositions 1 and 3 -/

/-- **Proposition 1.** Let F be local, Pareto and symmetric under every element
    of a group P of voter permutations, each together with some symmetry of the
    hexagon. Then the degrees are constant on the orbits of P and sum to 1, so
    every common divisor of the orbit sizes is 1. -/
theorem prop1 (hF : Local F) (hP : Pareto F) (P : Subgroup (Equiv.Perm ι))
    (hK : ∀ σ ∈ P, ∃ s t, Equivariant F σ s t) (c : ι → Fin 6) :
    (∀ σ ∈ P, ∀ i, deg F (σ i) c = deg F i c) ∧ ∑ i, deg F i c = 1 ∧
      ∀ g : ℕ, (∀ i, g ∣ orbSize P i) → g = 1 := by
  have hconst : ∀ σ ∈ P, ∀ i, deg F (σ i) c = deg F i c := fun σ hσ i => by
    obtain ⟨s, t, hE⟩ := hK σ hσ
    exact deg_perm hF hE i c
  refine ⟨hconst, deg_sum hF hP c, fun g hg => ?_⟩
  have h := dvd_sum_orbits P (fun i => deg F i c) hconst g hg
  rw [deg_sum hF hP c] at h
  exact Nat.dvd_one.mp (by exact_mod_cast h)

/-- **Proposition 3.** A local Pareto rule symmetric under every element of a
    set K of symmetries exists exactly when the voter permutations of K fix a
    common voter. Then that voter's dictatorship is such a rule. -/
theorem prop3 (K : Set (Equiv.Perm ι × Bool × Fin 6)) :
    (∃ F : (ι → Fin 6) → Fin 6, Local F ∧ Pareto F ∧ ∀ k ∈ K, Equivariant F k.1 k.2.1 k.2.2) ↔
      ∃ i, ∀ k ∈ K, k.1 i = i := by
  constructor
  · rintro ⟨F, hF, hP, hK⟩
    let c : ι → Fin 6 := fun _ => 0
    have hdeg : ∀ v, deg F v c = 0 ∨ deg F v c = 1 := fun v => by
      rcases deg_cases hF hP v c with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
    have hsum := deg_sum hF hP c
    obtain ⟨i, hi⟩ : ∃ i, deg F i c = 1 := by
      by_contra hno
      have hno : ∀ v, deg F v c ≠ 1 := fun v hv => hno ⟨v, hv⟩
      have : ∑ v, deg F v c = 0 :=
        sum_eq_zero fun v _ => (hdeg v).resolve_right (hno v)
      omega
    have huniq : ∀ j, deg F j c = 1 → j = i := by
      intro j hj
      by_contra hne
      have h2 : ∑ v ∈ {j, i}, deg F v c ≤ ∑ v, deg F v c :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun v _ _ => by
          rcases hdeg v with h | h <;> omega
      rw [sum_pair hne] at h2
      omega
    refine ⟨i, fun k hk => huniq _ ?_⟩
    rw [deg_perm hF (hK k hk) i c, hi]
  · rintro ⟨i, hi⟩
    refine ⟨fun π => π i, fun π j => ?_, fun π e b h => h i, fun k hk π => ?_⟩
    · show Adj (π i) (Function.update π j (π j + 1) i)
      by_cases hj : i = j
      · subst hj
        rw [Function.update_self]
        exact Or.inr (Or.inl rfl)
      · rw [Function.update_of_ne hj]
        exact Or.inl rfl
    · show hact k.2.1 k.2.2 (π (k.1.symm i)) = hact k.2.1 k.2.2 (π i)
      have hs : k.1.symm i = i := by
        nth_rewrite 1 [← hi k hk]
        simp
      rw [hs]

/-! ### Proposition 6 of *The Global Form*, for IIA rules -/

omit [Fintype ι] in
/-- Every IIA rule is local. -/
theorem local_of_iia (hF : GlobalForm.IIA F) : Local F := by
  intro π i
  have h := GlobalForm.steps_adjacent hF {i} π (π i)
  rwa [setS_self, setS_succ, setS_self] at h

/-- **Proposition 6 of *The Global Form*, for IIA rules into rankings.** The
    symmetries of the alternatives and reversal act on the degrees only
    through the voters they permute. -/
theorem prop6_iia (hF : GlobalForm.IIA F) {σ : Equiv.Perm ι} {s : Bool} {t : Fin 6}
    (hE : Equivariant F σ s t) (i : ι) (c : ι → Fin 6) : deg F (σ i) c = deg F i c :=
  deg_perm (local_of_iia hF) hE i c

/-- **Anonymity is the whole constraint.** A unanimous IIA rule symmetric under
    every permutation of the voters, each with any symmetry of the hexagon, has
    n · d = 1 for the common degree d, so n = 1. -/
theorem prop6_anonymous (hF : GlobalForm.IIA F) (hU : GlobalForm.Unanimous F)
    (hA : ∀ σ : Equiv.Perm ι, ∃ s t, Equivariant F σ s t) : Fintype.card ι = 1 := by
  let c : ι → Fin 6 := fun _ => 0
  have hsum := GlobalForm.degree_sum hF hU c
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i0⟩⟩
  · simp at hsum
  · have hall : ∀ v, deg F v c = deg F i0 c := fun v => by
      obtain ⟨s, t, hE⟩ := hA (Equiv.swap i0 v)
      have h := prop6_iia hF hE i0 c
      rwa [Equiv.swap_apply_left] at h
    rw [sum_congr rfl fun v _ => hall v, sum_const, card_univ, nsmul_eq_mul] at hsum
    exact_mod_cast Int.eq_one_of_mul_eq_one_right (by positivity) hsum

end LocalPareto

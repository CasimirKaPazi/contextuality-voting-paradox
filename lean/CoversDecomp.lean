/-
  Proposition 2 of *Covers and Division* (`notes/covers-and-division.md`,
  Section 2): every empirical model of a finite loop is a mixture of descents
  of symmetric models on finite covers, by flow decomposition.

  Encoding as in `Covers.lean`: one finite value type `V`, relations `R i`,
  contexts {x_i, x_{i+1}} with indices mod n. An empirical model gives each
  context i a distribution `e i x y` on pairs, periodic in i, supported on
  `R i`, and the two contexts at a variable give it the same marginal
  (`Model`). These are the circulations of the layered graph with total
  weight 1 (`Circ`).

  * `exists_walk`: from a node with positive outflow, following positive
    edges by a fixed choice never gets stuck, since inflow equals outflow.
    Two of its values at layer 0 agree, by pigeonhole, which closes a walk of
    k rounds: a global section of the k-fold cover (`Cyc`).
  * `decomp`: every circulation is a non-negative combination of such walks,
    each counted by how often it uses an edge in one period (`Cyc.cnt`). Each
    step removes as much of one walk as fits, the least ratio of weight to
    use, which leaves a circulation with fewer positive edges. Dividing by
    the use counts means walks need not be simple.
  * `prop2`: an empirical model is a mixture, with weights w · k summing to 1,
    of the models cnt / k, each a section of the k-fold cover. The model
    cnt / k is the descent of the uniform mixture of the k rotations of the
    section by the deck transformation: at context i it gives the pair (x, y)
    the share of rounds in which the section takes the values x, y there.
  * `model_of_section`, `model_iff_cover`: conversely, a global section of a
    finite cover gives an empirical model, so a loop has an empirical model
    exactly when some finite cover has a global section (the corollary, for
    relations of period n).

  Not formalised here: the bound k ≤ min |V_i| (it needs simple walks); the
  form with one ℤ/K-invariant distribution on the K-fold cover,
  K = lcm(1, …, m); and the corollary's statements in terms of the levels of
  obstruction.
-/

module

public import Covers

@[expose] public section

open Finset

namespace CoversDecomp

variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

/-! ### Circulations on the layered graph -/

/-- Weights f i x y on the edges from (i, x) to (i + 1, y), periodic in i,
    with inflow equal to outflow at every node. -/
structure Circ (n : ℕ) (f : ℕ → V → V → ℝ) : Prop where
  nonneg : ∀ i x y, 0 ≤ f i x y
  per : ∀ i, f (i + n) = f i
  cons : ∀ i y, ∑ x, f i x y = ∑ z, f (i + 1) y z

omit [DecidableEq V] in
lemma f_per_mul {f : ℕ → V → V → ℝ} (h : Circ n f) (i : ℕ) :
    ∀ q, f (i + q * n) = f i
  | 0 => by simp
  | q + 1 => by
    rw [show i + (q + 1) * n = i + q * n + n by ring, h.per, f_per_mul h i q]

omit [DecidableEq V] in
lemma f_mod {f : ℕ → V → V → ℝ} (h : Circ n f) (i : ℕ) : f i = f (i % n) := by
  conv_lhs => rw [← Nat.mod_add_div i n]
  rw [show i % n + n * (i / n) = i % n + i / n * n by ring, f_per_mul h]

omit [DecidableEq V] in
lemma total_succ {f : ℕ → V → V → ℝ} (h : Circ n f) (i : ℕ) :
    ∑ x, ∑ y, f (i + 1) x y = ∑ x, ∑ y, f i x y := by
  calc ∑ x, ∑ y, f (i + 1) x y = ∑ y, ∑ x, f i x y :=
        sum_congr rfl fun y _ => (h.cons i y).symm
    _ = ∑ x, ∑ y, f i x y := sum_comm

omit [DecidableEq V] in
lemma total_eq {f : ℕ → V → V → ℝ} (h : Circ n f) :
    ∀ i, ∑ x, ∑ y, f i x y = ∑ x, ∑ y, f 0 x y
  | 0 => rfl
  | i + 1 => by rw [total_succ h, total_eq h i]

/-! ### Closed walks -/

/-- A closed walk of k rounds around the loop: a sequence of values of period
    k · n, a candidate section of the k-fold cover. -/
structure Cyc (V : Type*) (n : ℕ) where
  k : ℕ
  hk : 0 < k
  s : ℕ → V
  per : ∀ m, s (m + k * n) = s m

/-- How often the walk uses the edge from (i, x) to (i + 1, y) in one period. -/
def Cyc.cnt (c : Cyc V n) (i : ℕ) (x y : V) : ℕ :=
  ∑ m ∈ range (c.k * n), if m % n = i % n ∧ c.s m = x ∧ c.s (m + 1) = y then 1 else 0

omit [Fintype V] in
lemma Cyc.cnt_add (c : Cyc V n) (i : ℕ) (x y : V) : c.cnt (i + n) x y = c.cnt i x y := by
  unfold Cyc.cnt
  rw [Nat.add_mod_right]

omit [Fintype V] in
lemma Cyc.cnt_mod (c : Cyc V n) (i : ℕ) (x y : V) : c.cnt (i % n) x y = c.cnt i x y := by
  unfold Cyc.cnt
  rw [Nat.mod_mod]

lemma sum_ind_mid (A B : Prop) [Decidable A] [Decidable B] (u : V) :
    ∑ x, (if A ∧ u = x ∧ B then 1 else 0 : ℕ) = if A ∧ B then 1 else 0 := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

lemma sum_ind_last (A : Prop) [Decidable A] (u v y : V) :
    ∑ z, (if A ∧ u = y ∧ v = z then 1 else 0 : ℕ) = if A ∧ u = y then 1 else 0 := by
  by_cases hA : A <;> by_cases hu : u = y <;> simp [hA, hu]

lemma sum_ind_eq (A : Prop) [Decidable A] (u : V) :
    ∑ x, (if A ∧ u = x then 1 else 0 : ℕ) = if A then 1 else 0 := by
  by_cases hA : A <;> simp [hA]

/-- A sum over one period of a periodic function is invariant under a shift by one. -/
lemma sum_shift (g : ℕ → ℕ) (p : ℕ) (hg : g p = g 0) :
    ∑ m ∈ range p, g (m + 1) = ∑ m ∈ range p, g m := by
  have h1 := sum_range_succ' g p
  have h2 := sum_range_succ g p
  omega

/-- A closed walk is itself a circulation: inflow equals outflow at every node. -/
lemma Cyc.cnt_cons (c : Cyc V n) (i : ℕ) (y : V) :
    ∑ x, c.cnt i x y = ∑ z, c.cnt (i + 1) y z := by
  unfold Cyc.cnt
  rw [sum_comm, sum_comm (s := univ)]
  have hL : ∀ m, ∑ x, (if m % n = i % n ∧ c.s m = x ∧ c.s (m + 1) = y then 1 else 0 : ℕ) =
      if m % n = i % n ∧ c.s (m + 1) = y then 1 else 0 := fun m => sum_ind_mid _ _ _
  have hR : ∀ m, ∑ z, (if m % n = (i + 1) % n ∧ c.s m = y ∧ c.s (m + 1) = z then 1 else 0 : ℕ) =
      if m % n = (i + 1) % n ∧ c.s m = y then 1 else 0 := fun m => sum_ind_last _ _ _ _
  simp only [hL, hR]
  have hmod : ∀ m, ((m + 1) % n = (i + 1) % n ↔ m % n = i % n) := fun m =>
    ⟨fun h => Nat.ModEq.add_right_cancel' 1 h, fun h => Nat.ModEq.add_right 1 h⟩
  have := sum_shift (fun m => if m % n = (i + 1) % n ∧ c.s m = y then 1 else 0) (c.k * n)
    (by
      have hs : c.s (c.k * n) = c.s 0 := by simpa using c.per 0
      simp only [Nat.mul_mod_left, Nat.zero_mod, hs]
      exact if_congr Iff.rfl rfl rfl)
  simp only [hmod] at this
  exact this

/-! ### Following positive edges -/

/-- A fixed choice of a positive edge out of x, if there is one. -/
noncomputable def nextOf (g : V → V → ℝ) (x : V) : V :=
  open Classical in if hx : ∃ y, 0 < g x y then hx.choose else x

/-- The walk from x₀ taking `step m` at step m. -/
def walk (step : ℕ → V → V) (x₀ : V) : ℕ → V
  | 0 => x₀
  | m + 1 => step m (walk step x₀ m)

omit [DecidableEq V] in
/-- From a node of layer 0 with positive outflow, the walk along positive edges
    closes after some rounds: a closed walk all of whose edges are positive. -/
theorem exists_walk {f : ℕ → V → V → ℝ} (h : Circ n f) (x₀ : V)
    (hx₀ : ∃ y, 0 < f 0 x₀ y) : ∃ c : Cyc V n, ∀ m, 0 < f (m % n) (c.s m) (c.s (m + 1)) := by
  let W := walk (fun m w => nextOf (f m) w) x₀
  have hW : ∀ m, W (m + 1) = nextOf (f m) (W m) := fun m => rfl
  -- every node of the walk has positive outflow, and every edge is positive
  have hpos : ∀ m, ∃ y, 0 < f m (W m) y := by
    intro m
    induction m with
    | zero => exact hx₀
    | succ m ih =>
      have he : 0 < f m (W m) (W (m + 1)) := by
        rw [hW]
        unfold nextOf
        split_ifs
        exact ih.choose_spec
      by_contra hno
      push Not at hno
      have h1 : ∑ z, f (m + 1) (W (m + 1)) z ≤ 0 := sum_nonpos fun z _ => hno z
      have h2 : f m (W m) (W (m + 1)) ≤ ∑ x, f m x (W (m + 1)) :=
        single_le_sum (fun x _ => h.nonneg m x (W (m + 1))) (mem_univ (W m))
      rw [h.cons] at h2
      linarith
  have hedge : ∀ m, 0 < f m (W m) (W (m + 1)) := by
    intro m
    rw [hW]
    unfold nextOf
    split_ifs with hh
    · exact hh.choose_spec
    · exact absurd (hpos m) hh
  -- two values at layer 0 agree
  obtain ⟨a', b', hab', heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun j : Fin (Fintype.card V + 1) => W (j.val * n)) (by simp)
  obtain ⟨a, b, hab, hW'⟩ : ∃ a b : ℕ, a < b ∧ W (a * n) = W (b * n) := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab') with h' | h'
    · exact ⟨a'.val, b'.val, h', heq⟩
    · exact ⟨b'.val, a'.val, h', heq.symm⟩
  -- from round a the walk repeats with period (b − a) · n
  have hper : ∀ m, W (a * n + m + (b - a) * n) = W (a * n + m) := by
    intro m
    induction m with
    | zero =>
      have : a * n + 0 + (b - a) * n = b * n := by
        rw [add_zero, ← add_mul, Nat.add_sub_cancel' hab.le]
      rw [this, add_zero]
      exact hW'.symm
    | succ m ih =>
      rw [show a * n + (m + 1) + (b - a) * n = a * n + m + (b - a) * n + 1 by ring,
        show a * n + (m + 1) = a * n + m + 1 by ring, hW, hW, ih, f_per_mul h]
  refine ⟨⟨b - a, by omega, fun m => W (a * n + m), fun m => ?_⟩, fun m => ?_⟩
  · show W (a * n + (m + (b - a) * n)) = W (a * n + m)
    rw [← add_assoc]
    exact hper m
  · show 0 < f (m % n) (W (a * n + m)) (W (a * n + m + 1))
    have := hedge (a * n + m)
    have hm : (a * n + m) % n = m % n := by rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    rwa [f_mod h (a * n + m), hm] at this

/-! ### Flow decomposition -/

omit [Fintype V] [DecidableEq V] in
lemma pos_of_sum_pos {ι : Type*} {s : Finset ι} {g : ι → ℝ} (h : 0 < ∑ i ∈ s, g i) :
    ∃ i ∈ s, 0 < g i := by
  by_contra hc
  push Not at hc
  have := sum_nonpos hc
  linarith

omit [Fintype V] [DecidableEq V] in
lemma pos_of_sum_pos_nat {ι : Type*} {s : Finset ι} {g : ι → ℕ} (h : 0 < ∑ i ∈ s, g i) :
    ∃ i ∈ s, 0 < g i := by
  by_contra hc
  push Not at hc
  have : ∑ i ∈ s, g i = 0 := sum_eq_zero fun i hi => by have := hc i hi; omega
  omega

/-- The number of positive edges. -/
noncomputable def suppCard (n : ℕ) (f : ℕ → V → V → ℝ) : ℕ :=
  ((range n ×ˢ (univ ×ˢ univ)).filter fun e : ℕ × V × V => f e.1 e.2.1 e.2.2 ≠ 0).card

/-- **Flow decomposition.** A circulation is a non-negative combination of
    closed walks along its positive edges, each weighted by its use of an edge. -/
theorem decomp (hn : 0 < n) :
    ∀ N (f : ℕ → V → V → ℝ), Circ n f → suppCard n f = N →
      ∃ L : List (ℝ × Cyc V n),
        (∀ c ∈ L, 0 ≤ c.1 ∧ ∀ m, 0 < f (m % n) (c.2.s m) (c.2.s (m + 1))) ∧
        ∀ i x y, f i x y = (L.map fun c => c.1 * (c.2.cnt i x y : ℝ)).sum := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro f h hN
    by_cases hz : ∀ i < n, ∀ x y, f i x y = 0
    · refine ⟨[], by simp, fun i x y => ?_⟩
      rw [f_mod h i]
      simp [hz (i % n) (Nat.mod_lt i hn)]
    push Not at hz
    obtain ⟨i₀, hi₀, x₁, y₁, hne⟩ := hz
    have hpos₁ : 0 < f i₀ x₁ y₁ := lt_of_le_of_ne (h.nonneg _ _ _) (Ne.symm hne)
    -- some edge of layer 0 is positive
    have hT : 0 < ∑ x, ∑ y, f 0 x y := by
      rw [← total_eq h i₀]
      have := single_le_sum (f := fun x => ∑ y, f i₀ x y)
        (fun x _ => sum_nonneg fun y _ => h.nonneg i₀ x y) (mem_univ x₁)
      have := single_le_sum (f := fun y => f i₀ x₁ y) (fun y _ => h.nonneg i₀ x₁ y) (mem_univ y₁)
      linarith
    obtain ⟨x₀, -, hx₀⟩ := pos_of_sum_pos hT
    obtain ⟨y₀, -, hy₀⟩ := pos_of_sum_pos hx₀
    obtain ⟨c, hc⟩ := exists_walk h x₀ ⟨y₀, hy₀⟩
    -- edges used by the walk are positive
    have hcpos : ∀ i x y, 0 < c.cnt i x y → 0 < f i x y := by
      intro i x y hcnt
      unfold Cyc.cnt at hcnt
      obtain ⟨m, -, hm⟩ := pos_of_sum_pos_nat hcnt
      have hm' : m % n = i % n ∧ c.s m = x ∧ c.s (m + 1) = y := by
        by_contra hcon
        simp [hcon] at hm
      obtain ⟨h1, h2, h3⟩ := hm'
      rw [f_mod h i, ← h1, ← h2, ← h3]
      exact hc m
    -- the least ratio of weight to use along the walk
    let E := (range n ×ˢ (univ ×ˢ univ)).filter
      fun e : ℕ × V × V => 0 < c.cnt e.1 e.2.1 e.2.2
    have hE : E.Nonempty := by
      refine ⟨(0, c.s 0, c.s 1), ?_⟩
      simp only [E, mem_filter, mem_product, mem_range, mem_univ, and_true]
      refine ⟨hn, ?_⟩
      unfold Cyc.cnt
      simp only [Nat.zero_mod]
      have := single_le_sum (f := fun m => (if m % n = 0 % n ∧ c.s m = c.s 0 ∧
        c.s (m + 1) = c.s 1 then 1 else 0 : ℕ)) (fun _ _ => Nat.zero_le _)
        (mem_range.mpr (Nat.mul_pos c.hk hn))
      simp only [Nat.zero_mod, and_self, ↓reduceIte] at this
      omega
    obtain ⟨e₀, he₀, hmin⟩ := E.exists_min_image
      (fun e => f e.1 e.2.1 e.2.2 / (c.cnt e.1 e.2.1 e.2.2 : ℝ)) hE
    set t := f e₀.1 e₀.2.1 e₀.2.2 / (c.cnt e₀.1 e₀.2.1 e₀.2.2 : ℝ) with ht
    simp only [E, mem_filter, mem_product, mem_range, mem_univ, and_true] at he₀
    have hcnt₀ : (0 : ℝ) < c.cnt e₀.1 e₀.2.1 e₀.2.2 := by exact_mod_cast he₀.2
    have ht0 : 0 ≤ t := div_nonneg (h.nonneg _ _ _) hcnt₀.le
    -- removing t times the walk
    let f' : ℕ → V → V → ℝ := fun i x y => f i x y - t * c.cnt i x y
    have hle : ∀ i x y, t * c.cnt i x y ≤ f i x y := by
      intro i x y
      by_cases hci : c.cnt i x y = 0
      · rw [hci, Nat.cast_zero, mul_zero]
        exact h.nonneg i x y
      · have hci' : 0 < c.cnt (i % n) x y := by rw [Cyc.cnt_mod]; omega
        have hmem : (i % n, x, y) ∈ E := by
          simp only [E, mem_filter, mem_product, mem_range, mem_univ, and_true]
          exact ⟨Nat.mod_lt i hn, hci'⟩
        have := hmin _ hmem
        simp only at this
        rw [Cyc.cnt_mod, ← f_mod h i] at this
        have hpos' : (0 : ℝ) < c.cnt i x y := by exact_mod_cast Nat.pos_of_ne_zero hci
        rw [le_div_iff₀ hpos'] at this
        exact this
    have hf' : Circ n f' := by
      refine ⟨fun i x y => by simp only [f']; linarith [hle i x y], fun i => ?_, fun i y => ?_⟩
      · funext x y
        simp only [f', h.per, Cyc.cnt_add]
      · simp only [f', sum_sub_distrib, ← mul_sum]
        rw [h.cons i y]
        have := c.cnt_cons i y
        have hc' : (∑ x, (c.cnt i x y : ℝ)) = ∑ z, (c.cnt (i + 1) y z : ℝ) := by
          exact_mod_cast this
        rw [hc']
    -- fewer positive edges
    have hlt : suppCard n f' < N := by
      rw [← hN]
      unfold suppCard
      apply card_lt_card
      rw [ssubset_iff_of_subset]
      · refine ⟨e₀, ?_, ?_⟩
        · simp only [mem_filter, mem_product, mem_range, mem_univ, and_true]
          exact ⟨he₀.1, (hcpos _ _ _ he₀.2).ne'⟩
        · simp only [mem_filter, mem_product, mem_range, mem_univ, and_true, not_and,
            not_not, f']
          intro _
          rw [ht]
          field_simp
          ring
      · intro e he
        simp only [mem_filter, mem_product, mem_range, mem_univ, and_true] at he ⊢
        refine ⟨he.1, fun h0 => he.2 ?_⟩
        simp only [f']
        have := mul_nonneg ht0 (Nat.cast_nonneg (α := ℝ) (c.cnt e.1 e.2.1 e.2.2))
        have := hf'.nonneg e.1 e.2.1 e.2.2
        simp only [f'] at this
        linarith
    obtain ⟨L, hL, hLeq⟩ := ih _ hlt f' hf' rfl
    refine ⟨(t, c) :: L, ?_, fun i x y => ?_⟩
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨ht0, hc⟩
      · refine ⟨(hL d hd).1, fun m => ?_⟩
        have := (hL d hd).2 m
        have := mul_nonneg ht0
          (Nat.cast_nonneg (α := ℝ) (c.cnt (m % n) (d.2.s m) (d.2.s (m + 1))))
        simp only [f'] at *
        linarith
    · rw [List.map_cons, List.sum_cons, ← hLeq i x y]
      simp only [f']
      ring

/-! ### Proposition 2 -/

/-- An empirical model of the loop: a distribution on R i for each context i,
    periodic in i, with equal marginals on shared variables. -/
structure Model (R : ℕ → V → V → Prop) (n : ℕ) (e : ℕ → V → V → ℝ) : Prop where
  circ : Circ n e
  total : ∑ x, ∑ y, e 0 x y = 1
  supp : ∀ i x y, 0 < e i x y → R i x y

lemma count_layer0 (hn : 0 < n) (k : ℕ) :
    ∑ m ∈ range (k * n), (if m % n = 0 then 1 else 0 : ℕ) = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * n = k * n + n by ring, sum_range_add, ih]
    have : ∑ j ∈ range n, (if (k * n + j) % n = 0 then 1 else 0 : ℕ) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j hj hj0
        have hjn := mem_range.mp hj
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hjn]
        simp [hj0]
      · intro h0
        exact absurd (mem_range.mpr hn) h0
    rw [this]

/-- A walk of k rounds uses k edges of each layer in one period. -/
lemma Cyc.total_cnt (hn : 0 < n) (c : Cyc V n) : ∑ x, ∑ y, (c.cnt 0 x y : ℝ) = c.k := by
  have : ∑ x, ∑ y, c.cnt 0 x y = c.k := by
    unfold Cyc.cnt
    calc _ = ∑ x, ∑ m ∈ range (c.k * n), ∑ y,
          (if m % n = 0 % n ∧ c.s m = x ∧ c.s (m + 1) = y then 1 else 0 : ℕ) :=
          sum_congr rfl fun x _ => sum_comm
      _ = ∑ m ∈ range (c.k * n), ∑ x, ∑ y,
          (if m % n = 0 % n ∧ c.s m = x ∧ c.s (m + 1) = y then 1 else 0 : ℕ) := sum_comm
      _ = ∑ m ∈ range (c.k * n), (if m % n = 0 then 1 else 0 : ℕ) := by
          refine sum_congr rfl fun m _ => ?_
          simp only [Nat.zero_mod]
          exact (sum_congr rfl fun x _ => sum_ind_last (m % n = 0) (c.s m) (c.s (m + 1)) x).trans
            (sum_ind_eq (m % n = 0) (c.s m))
      _ = c.k := count_layer0 hn c.k
  exact_mod_cast this

/-- Totals commute with the sum over the list of walks. -/
lemma sum_list (L : List (ℝ × Cyc V n)) (i : ℕ) :
    ∑ x, ∑ y, (L.map fun c => c.1 * (c.2.cnt i x y : ℝ)).sum =
      (L.map fun c => ∑ x, ∑ y, c.1 * (c.2.cnt i x y : ℝ)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, sum_add_distrib, ih]

/-- **Proposition 2.** An empirical model of a finite loop is a mixture of
    descents of symmetric models on finite covers: there are closed walks c,
    each a global section of its c.k-fold cover, and weights w ≥ 0 with
    Σ w · c.k = 1, such that the model gives context i the pair (x, y) with
    probability Σ (w · c.k) · (c.cnt i x y / c.k), where c.cnt i x y / c.k is
    the descent of the uniform mixture of the rotations of c. -/
theorem prop2 (hn : 0 < n) {R : ℕ → V → V → Prop} {e : ℕ → V → V → ℝ} (h : Model R n e) :
    ∃ L : List (ℝ × Cyc V n),
      (∀ c ∈ L, 0 ≤ c.1 ∧ Covers.IsSection (Covers.Cover R n) (c.2.k * n) c.2.s) ∧
      (L.map fun c => c.1 * (c.2.k : ℝ)).sum = 1 ∧
      ∀ i x y, e i x y = (L.map fun c => (c.1 * (c.2.k : ℝ)) * ((c.2.cnt i x y : ℝ) / c.2.k)).sum := by
  obtain ⟨L, hL, hLeq⟩ := decomp hn _ e h.circ rfl
  refine ⟨L, fun c hc => ⟨(hL c hc).1, fun m => c.2.per m, fun m => ?_⟩, ?_, fun i x y => ?_⟩
  · rw [Covers.cover_mod]
    exact h.supp _ _ _ ((hL c hc).2 m)
  · have htot := h.total
    simp only [hLeq 0, sum_list] at htot
    rw [← htot]
    congr 1
    refine List.map_congr_left fun c _ => ?_
    simp only [← mul_sum]
    rw [c.2.total_cnt hn]
  · rw [hLeq i x y]
    congr 1
    refine List.map_congr_left fun c _ => ?_
    have hk : (c.2.k : ℝ) ≠ 0 := by exact_mod_cast c.2.hk.ne'
    field_simp

/-! ### The converse of division -/

/-- A global section of the k-fold cover gives an empirical model: at context
    i, the share of rounds in which the section takes the values x, y. This
    needs the relations to have period n. -/
theorem model_of_section (hn : 0 < n) {R : ℕ → V → V → Prop} (hR : ∀ i, R i = R (i % n))
    (c : Cyc V n) (hc : ∀ m, R (m % n) (c.s m) (c.s (m + 1))) :
    Model R n (fun i x y => (c.cnt i x y : ℝ) / c.k) := by
  have hk : (c.k : ℝ) ≠ 0 := by exact_mod_cast c.hk.ne'
  refine ⟨⟨fun i x y => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), fun i => ?_,
    fun i y => ?_⟩, ?_, fun i x y hpos => ?_⟩
  · funext x y
    simp only [Cyc.cnt_add]
  · simp only [← sum_div]
    congr 1
    exact_mod_cast c.cnt_cons i y
  · simp only [← sum_div]
    rw [c.total_cnt hn]
    exact div_self hk
  · have hpos' : 0 < (c.cnt i x y : ℝ) / c.k := hpos
    have hcnt : 0 < c.cnt i x y := by
      rcases Nat.eq_zero_or_pos (c.cnt i x y) with h0 | h0
      · rw [h0] at hpos'
        simp at hpos'
      · exact h0
    unfold Cyc.cnt at hcnt
    obtain ⟨m, -, hm⟩ := pos_of_sum_pos_nat hcnt
    have hm' : m % n = i % n ∧ c.s m = x ∧ c.s (m + 1) = y := by
      by_contra hcon
      simp [hcon] at hm
    obtain ⟨h1, h2, h3⟩ := hm'
    rw [hR i, ← h1, ← h2, ← h3]
    exact hc m

/-- **Corollary.** A loop with relations of period n has an empirical model
    exactly when some finite cover has a global section. -/
theorem model_iff_cover (hn : 0 < n) {R : ℕ → V → V → Prop} (hR : ∀ i, R i = R (i % n)) :
    (∃ e, Model R n e) ↔
      ∃ k, 0 < k ∧ ∃ f, Covers.IsSection (Covers.Cover R n) (k * n) f := by
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨L, hL, hsum, -⟩ := prop2 hn he
    match L, hL, hsum with
    | [], _, hsum => simp at hsum
    | c :: _, hL, _ => exact ⟨c.2.k, c.2.hk, c.2.s, (hL c List.mem_cons_self).2⟩
  · rintro ⟨k, hk, f, hper, hrel⟩
    refine ⟨_, model_of_section hn hR ⟨k, hk, f, hper⟩ fun m => ?_⟩
    have := hrel m
    rwa [Covers.cover_mod] at this

end CoversDecomp

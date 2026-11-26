/-
  Section 7 of *The Global Form* (`notes/global-form.md`): Lemmas 5 and 6 and
  Proposition 3, the degree for strategy-proof rules, three alternatives, any
  finite set of voters. With unanimity this is the Gibbard–Satterthwaite
  theorem for three alternatives (`gs`).

  A rule G sends profiles of rankings (positions on the hexagon of
  `GlobalForm.lean`) to one of the outcomes a, b, c (`Fin 3`), placed on a
  triangle oriented a → b → c → a. The winding of the outcome while a block S
  of voters walks once around is `W3 G S c`; a full turn is 3, and the degree
  is `degSP G i c = W3 G {i} c / 3`.

  * Swap lemma (`swap_step`, `block_step`): when a voter, or a block of voters
    together, takes step k of the loop, raising y over x, a strategy-proof rule
    keeps the outcome or moves it from x to y (`Perm k`). This is a finite fact
    about three outcomes (`swap_fin`), applied to strategy-proofness in both
    directions; blocks follow by induction, since permitted moves compose.
  * Squares: around a square of steps of two blocks the winding is 0
    (`square_fin`, finite). Summing squares on the 6 × 6 grid of positions of
    two blocks (`GridOK`), the rows have equal windings (`rows_eq`) and the
    diagonal winds as row 0 plus column 0 (`diag`).
  * Rigidity (`rigid`, finite over all walks with permitted steps): a walk
    winds 0 or 3, and 3 only when the outcome is the walkers' top throughout.

  Results:
  * `lemma5`: the degree does not depend on the context, the diagonal winds
    3 times the sum of the degrees (`lemma5_sum`), and with unanimity the
    degrees sum to 1 (`degree_sum`);
  * `lemma6`: every degree is 0 or 1, and 1 exactly when the outcome is the
    voter's top at every step of the loop (`top_of_deg`);
  * `prop3`: all degrees are 0, or one voter has degree 1, the others 0, and
    the rule is that voter's dictatorship;
  * `gs`: with unanimity, a strategy-proof rule is a dictatorship.
-/

module

public import GlobalForm

@[expose] public section

open Finset GlobalForm

namespace GlobalFormSP

/-! ### Rankings and outcomes -/

/-- The positions of a, b, c in the rankings abc, bac, bca, cba, cab, acb. -/
def posTbl : List (List Nat) :=
  [[0, 1, 2], [1, 0, 2], [2, 0, 1], [2, 1, 0], [1, 2, 0], [0, 2, 1]]

def rpos (k : Fin 6) (x : Fin 3) : Nat := (posTbl.getD k.val []).getD x.val 0

/-- Ranking k strictly prefers x to y. -/
def pref (k : Fin 6) (x y : Fin 3) : Prop := rpos k x < rpos k y

instance (k : Fin 6) (x y : Fin 3) : Decidable (pref k x y) := by unfold pref; infer_instance

/-- The top of ranking k. -/
def top (k : Fin 6) : Fin 3 :=
  match k.val with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | _ => 0

/-- Step k of the loop raises `mvTo k` over `mvFrom k`. -/
def mvFrom (k : Fin 6) : Fin 3 :=
  match k.val with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | _ => 2

def mvTo (k : Fin 6) : Fin 3 :=
  match k.val with
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 0
  | 4 => 0
  | _ => 1

/-- The moves permitted at step k: stay, or from `mvFrom k` to `mvTo k`. -/
def Perm (k : Fin 6) (o o' : Fin 3) : Prop := o' = o ∨ (o = mvFrom k ∧ o' = mvTo k)

instance (k : Fin 6) (o o' : Fin 3) : Decidable (Perm k o o') := by unfold Perm; infer_instance

/-- A step on the triangle: +1 forward, −1 backward. -/
def d3 (a b : Fin 3) : ℤ := if b = a + 1 then 1 else if a = b + 1 then -1 else 0

/-- The winding of a closed walk of six steps on the triangle (a full turn is 3). -/
def wind3 (w : Fin 6 → Fin 3) : ℤ :=
  d3 (w 0) (w 1) + d3 (w 1) (w 2) + d3 (w 2) (w 3) + d3 (w 3) (w 4) + d3 (w 4) (w 5) +
    d3 (w 5) (w 0)

/-! ### Finite facts -/

/-- Strategy-proofness in both directions across step k leaves only the permitted move. -/
lemma swap_fin : ∀ (k : Fin 6) (o o' : Fin 3), ¬ pref k o' o → ¬ pref (k + 1) o o' →
    Perm k o o' := by decide

lemma perm_trans : ∀ (k : Fin 6) (a b c : Fin 3), Perm k a b → Perm k b c → Perm k a c := by
  decide

lemma comp_fin : ∀ (k : Fin 6) (a b c : Fin 3), Perm k a b → Perm k b c →
    d3 a c = d3 a b + d3 b c := by decide

def SqOK (k l : Fin 6) (a0 a1 b0 b1 : Fin 3) : Prop :=
  Perm k a0 a1 → Perm k b0 b1 → Perm l a0 b0 → Perm l a1 b1 →
    d3 a0 a1 + d3 a1 b1 = d3 a0 b0 + d3 b0 b1

instance (k l : Fin 6) (a0 a1 b0 b1 : Fin 3) : Decidable (SqOK k l a0 a1 b0 b1) := by
  unfold SqOK; infer_instance

/-- Around a square of permitted steps the winding is 0. -/
lemma square_fin : ∀ (k l : Fin 6) (a0 a1 b0 b1 : Fin 3), SqOK k l a0 a1 b0 b1 := by
  decide +kernel

/-- A walk given by its six values. -/
def mk6 (w0 w1 w2 w3 w4 w5 : Fin 3) : Fin 6 → Fin 3 := fun k =>
  match k.val with
  | 0 => w0
  | 1 => w1
  | 2 => w2
  | 3 => w3
  | 4 => w4
  | _ => w5

def RigOK (w : Fin 6 → Fin 3) : Prop :=
  (∀ k : Fin 6, Perm k (w k) (w (k + 1))) →
    (wind3 w = 0 ∨ wind3 w = 3) ∧ (wind3 w = 3 → ∀ k, w k = top k)

instance (w : Fin 6 → Fin 3) : Decidable (RigOK w) := by unfold RigOK; infer_instance

lemma rig_all : ∀ w0 w1 w2 w3 w4 w5 : Fin 3, RigOK (mk6 w0 w1 w2 w3 w4 w5) := by
  decide +kernel

/-- **Rigidity on the triangle.** A walk with permitted steps winds 0 or 3,
    and 3 only along the tops. -/
theorem rigid (w : Fin 6 → Fin 3) : RigOK w := by
  have h := rig_all (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)
  have e : mk6 (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) = w := by
    funext k
    fin_cases k <;> rfl
  rwa [e] at h

lemma wind3_top : wind3 top = 3 := by decide

lemma d3_self : ∀ a : Fin 3, d3 a a = 0 := by decide

/-! ### Grids of two blocks -/

/-- Outcomes on the grid of positions of two blocks: horizontal steps are
    steps of the first block, vertical steps of the second. -/
def GridOK (O : Fin 6 → Fin 6 → Fin 3) : Prop :=
  (∀ a b, Perm a (O a b) (O (a + 1) b)) ∧ (∀ a b, Perm b (O a b) (O a (b + 1)))

section Grid

variable (O : Fin 6 → Fin 6 → Fin 3) (h : GridOK O)
include h

lemma sq {a a' b b' : Fin 6} (ha : a' = a + 1) (hb : b' = b + 1) :
    d3 (O a b) (O a' b) + d3 (O a' b) (O a' b') = d3 (O a b) (O a b') + d3 (O a b') (O a' b') := by
  subst ha hb
  exact square_fin a b _ _ _ _ (h.1 a b) (h.1 a (b + 1)) (h.2 a b) (h.2 (a + 1) b)

lemma comp {k k' : Fin 6} (hk : k' = k + 1) :
    d3 (O k k) (O k' k') = d3 (O k k) (O k' k) + d3 (O k' k) (O k' k') := by
  subst hk
  exact comp_fin k _ _ _ (h.1 k k) (h.2 (k + 1) k)

/-- Neighbouring rows wind equally. -/
lemma row_const (b b' : Fin 6) (hb : b' = b + 1) :
    wind3 (fun a => O a b) = wind3 (fun a => O a b') := by
  have s0 := sq O h (a := 0) (a' := 1) rfl hb
  have s1 := sq O h (a := 1) (a' := 2) rfl hb
  have s2 := sq O h (a := 2) (a' := 3) rfl hb
  have s3 := sq O h (a := 3) (a' := 4) rfl hb
  have s4 := sq O h (a := 4) (a' := 5) rfl hb
  have s5 := sq O h (a := 5) (a' := 0) rfl hb
  simp only [wind3]
  linarith

/-- All rows wind equally. -/
lemma rows_eq (p : Fin 6) : wind3 (fun a => O a p) = wind3 (fun a => O a 0) := by
  have r0 := row_const O h 0 1 rfl
  have r1 := row_const O h 1 2 rfl
  have r2 := row_const O h 2 3 rfl
  have r3 := row_const O h 3 4 rfl
  have r4 := row_const O h 4 5 rfl
  fin_cases p
  · rfl
  · exact r0.symm
  · exact (r0.trans r1).symm
  · exact (r0.trans (r1.trans r2)).symm
  · exact (r0.trans (r1.trans (r2.trans r3))).symm
  · exact (r0.trans (r1.trans (r2.trans (r3.trans r4)))).symm

/-- The diagonal winds as row 0 plus column 0 (15 squares below the diagonal). -/
lemma diag :
    wind3 (fun k => O k k) = wind3 (fun a => O a 0) + wind3 (fun b => O 0 b) := by
  have c0 := comp O h (k := 0) (k' := 1) rfl
  have c1 := comp O h (k := 1) (k' := 2) rfl
  have c2 := comp O h (k := 2) (k' := 3) rfl
  have c3 := comp O h (k := 3) (k' := 4) rfl
  have c4 := comp O h (k := 4) (k' := 5) rfl
  have c5 := comp O h (k := 5) (k' := 0) rfl
  have s10 := sq O h (a := 1) (a' := 2) (b := 0) (b' := 1) rfl rfl
  have s20 := sq O h (a := 2) (a' := 3) (b := 0) (b' := 1) rfl rfl
  have s21 := sq O h (a := 2) (a' := 3) (b := 1) (b' := 2) rfl rfl
  have s30 := sq O h (a := 3) (a' := 4) (b := 0) (b' := 1) rfl rfl
  have s31 := sq O h (a := 3) (a' := 4) (b := 1) (b' := 2) rfl rfl
  have s32 := sq O h (a := 3) (a' := 4) (b := 2) (b' := 3) rfl rfl
  have s40 := sq O h (a := 4) (a' := 5) (b := 0) (b' := 1) rfl rfl
  have s41 := sq O h (a := 4) (a' := 5) (b := 1) (b' := 2) rfl rfl
  have s42 := sq O h (a := 4) (a' := 5) (b := 2) (b' := 3) rfl rfl
  have s43 := sq O h (a := 4) (a' := 5) (b := 3) (b' := 4) rfl rfl
  have s50 := sq O h (a := 5) (a' := 0) (b := 0) (b' := 1) rfl rfl
  have s51 := sq O h (a := 5) (a' := 0) (b := 1) (b' := 2) rfl rfl
  have s52 := sq O h (a := 5) (a' := 0) (b := 2) (b' := 3) rfl rfl
  have s53 := sq O h (a := 5) (a' := 0) (b := 3) (b' := 4) rfl rfl
  have s54 := sq O h (a := 5) (a' := 0) (b := 4) (b' := 5) rfl rfl
  simp only [wind3]
  linarith

end Grid

/-! ### Strategy-proof rules -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Strategy-proofness: no voter strictly prefers the outcome of a misreport. -/
def SP (G : (ι → Fin 6) → Fin 3) : Prop :=
  ∀ (π : ι → Fin 6) (i : ι) (r : Fin 6), ¬ pref (π i) (G (setS {i} r π)) (G π)

/-- Unanimity: if all voters hold one ranking, its top is the outcome. -/
def UnanimousSP (G : (ι → Fin 6) → Fin 3) : Prop := ∀ k, G (fun _ => k) = top k

/-- The winding of the outcome while S walks once around, the others at c. -/
def W3 (G : (ι → Fin 6) → Fin 3) (S : Finset ι) (c : ι → Fin 6) : ℤ :=
  wind3 fun k => G (setS S k c)

/-- The degree of voter i at context c. -/
def degSP (G : (ι → Fin 6) → Fin 3) (i : ι) (c : ι → Fin 6) : ℤ := W3 G {i} c / 3

variable {G : (ι → Fin 6) → Fin 3}

omit [Fintype ι] in
lemma setS_apply_self (i : ι) (k : Fin 6) (c : ι → Fin 6) : setS {i} k c i = k := by
  unfold setS
  simp

omit [Fintype ι] in
/-- **Swap lemma.** A step of one voter keeps the outcome or makes the permitted move. -/
lemma swap_step (hG : SP G) (i : ι) (d : ι → Fin 6) (k : Fin 6) :
    Perm k (G (setS {i} k d)) (G (setS {i} (k + 1) d)) := by
  apply swap_fin k
  · have := hG (setS {i} k d) i (k + 1)
    rwa [setS_setS, setS_apply_self] at this
  · have := hG (setS {i} (k + 1) d) i k
    rwa [setS_setS, setS_apply_self] at this

omit [Fintype ι] in
/-- The swap lemma for a block walking together. -/
lemma block_step (hG : SP G) (S : Finset ι) :
    ∀ (d : ι → Fin 6) (k : Fin 6), Perm k (G (setS S k d)) (G (setS S (k + 1) d)) := by
  induction S using Finset.induction_on with
  | empty =>
    intro d k
    have e : ∀ m, setS (∅ : Finset ι) m d = d := fun m => by
      funext x
      unfold setS
      simp
    rw [e, e]
    exact Or.inl rfl
  | @insert j S hj ih =>
    intro d k
    have hd : Disjoint S {j} := Finset.disjoint_singleton_right.mpr hj
    have e : ∀ m, setS (insert j S) m d = setS {j} m (setS S m d) := fun m => by
      rw [Finset.insert_eq, Finset.union_comm, setS_union]
    rw [e, e]
    have h1 := swap_step hG j (setS S k d) k
    have h2 := ih (setS {j} (k + 1) d) k
    rw [setS_comm hd k (k + 1) d, setS_comm hd (k + 1) (k + 1) d] at h2
    exact perm_trans k _ _ _ h1 h2

omit [Fintype ι] in
lemma grid_ok (hG : SP G) (S T : Finset ι) (hST : Disjoint S T) (c : ι → Fin 6) :
    GridOK (fun a b => G (setS S a (setS T b c))) := by
  refine ⟨fun a b => block_step hG S (setS T b c) a, fun a b => ?_⟩
  show Perm b (G (setS S a (setS T b c))) (G (setS S a (setS T (b + 1) c)))
  rw [setS_comm hST, setS_comm hST]
  exact block_step hG T (setS S a c) b

omit [Fintype ι] in
/-- The square of two disjoint blocks. -/
theorem two_block (hG : SP G) (S T : Finset ι) (hST : Disjoint S T) (c : ι → Fin 6) :
    W3 G (S ∪ T) c = W3 G S (setS T 0 c) + W3 G T (setS S 0 c) := by
  have hd := diag _ (grid_ok hG S T hST c)
  unfold W3
  have e1 : (fun k => G (setS (S ∪ T) k c)) = fun k => G (setS S k (setS T k c)) :=
    funext fun k => by rw [setS_union, ← setS_comm hST]
  have e2 : (fun b => G (setS T b (setS S 0 c))) = fun b => G (setS S 0 (setS T b c)) :=
    funext fun b => by rw [setS_comm hST]
  rw [e1, e2]
  exact hd

/-! ### Lemma 5: invariance and sum -/

omit [Fintype ι] in
lemma W3_upd (hG : SP G) (S : Finset ι) (j : ι) (c : ι → Fin 6) (p : Fin 6) :
    W3 G S (setS {j} p c) = W3 G S c := by
  by_cases hj : j ∈ S
  · unfold W3
    congr 1
    funext k
    congr 1
    funext i
    unfold setS
    by_cases hi : i ∈ S
    · simp [hi]
    · have : i ≠ j := fun h => hi (h ▸ hj)
      simp [hi, this]
  · have hd : Disjoint S {j} := Finset.disjoint_singleton_right.mpr hj
    have hg := grid_ok hG S {j} hd c
    have h1 := rows_eq _ hg p
    have h2 := rows_eq _ hg (c j)
    have h3 : W3 G S (setS {j} p c) = W3 G S (setS {j} (c j) c) := h1.trans h2.symm
    rw [setS_self] at h3
    exact h3

/-- The winding of a block does not depend on where the other voters stand. -/
theorem W3_indep (hG : SP G) (S : Finset ι) (c c' : ι → Fin 6) : W3 G S c = W3 G S c' := by
  have key : ∀ U : Finset ι, W3 G S c = W3 G S (fun i => if i ∈ U then c' i else c i) := by
    intro U
    induction U using Finset.induction_on with
    | empty => simp
    | @insert j U _ ih =>
      rw [ih]
      have : (fun i => if i ∈ insert j U then c' i else c i) =
          setS {j} (c' j) (fun i => if i ∈ U then c' i else c i) := by
        funext i
        unfold setS
        by_cases hij : i = j
        · subst hij
          simp
        · simp [hij]
      rw [this, W3_upd hG]
  have := key univ
  simpa using this

/-- **Lemma 5 (invariance).** The degree does not depend on the context. -/
theorem lemma5 (hG : SP G) (i : ι) (c c' : ι → Fin 6) : degSP G i c = degSP G i c' := by
  unfold degSP
  rw [W3_indep hG {i} c c']

omit [Fintype ι] in
lemma W3_empty (c : ι → Fin 6) : W3 G ∅ c = 0 := by
  unfold W3
  have : (fun k => G (setS ∅ k c)) = fun _ => G c := by
    funext k
    unfold setS
    simp
  rw [this]
  simp [wind3, d3_self]

theorem W3_sum (hG : SP G) (S : Finset ι) (c : ι → Fin 6) :
    W3 G S c = ∑ i ∈ S, W3 G {i} c := by
  induction S using Finset.induction_on with
  | empty => simp [W3_empty]
  | @insert j S hj ih =>
    rw [sum_insert hj, ← ih]
    have hd : Disjoint S {j} := Finset.disjoint_singleton_right.mpr hj
    rw [show insert j S = S ∪ {j} by rw [Finset.insert_eq, Finset.union_comm],
      two_block hG S {j} hd c, W3_upd hG S j c 0, W3_indep hG {j} (setS S 0 c) c]
    ring

/-! ### Lemma 6: rigidity -/

omit [Fintype ι] in
theorem W3_cases (hG : SP G) (S : Finset ι) (c : ι → Fin 6) : W3 G S c = 0 ∨ W3 G S c = 3 :=
  (rigid (fun k => G (setS S k c)) (fun k => block_step hG S c k)).1

omit [Fintype ι] in
/-- A block of winding 3 gets its top at every step of its loop. -/
theorem top_of_W3 (hG : SP G) (S : Finset ι) (c : ι → Fin 6) (h : W3 G S c = 3) (k : Fin 6) :
    G (setS S k c) = top k :=
  (rigid (fun k => G (setS S k c)) (fun k => block_step hG S c k)).2 h k

omit [Fintype ι] in
theorem three_deg (hG : SP G) (i : ι) (c : ι → Fin 6) : W3 G {i} c = 3 * degSP G i c := by
  unfold degSP
  rcases W3_cases hG {i} c with h | h <;> rw [h] <;> norm_num

omit [Fintype ι] in
/-- **Lemma 6 (rigidity).** Every degree is 0 or 1. -/
theorem lemma6 (hG : SP G) (i : ι) (c : ι → Fin 6) : degSP G i c = 0 ∨ degSP G i c = 1 := by
  unfold degSP
  rcases W3_cases hG {i} c with h | h <;> rw [h] <;> norm_num

omit [Fintype ι] in
/-- A voter of degree 1 gets its top at every step of its loop. -/
theorem top_of_deg (hG : SP G) (i : ι) (c : ι → Fin 6) (h : degSP G i c = 1) (k : Fin 6) :
    G (setS {i} k c) = top k :=
  top_of_W3 hG {i} c (by rw [three_deg hG, h]; norm_num) k

/-- **Lemma 5 (sum).** The diagonal loop winds 3 times the sum of the degrees. -/
theorem lemma5_sum (hG : SP G) (c : ι → Fin 6) : W3 G univ c = 3 * ∑ i, degSP G i c := by
  rw [W3_sum hG, mul_sum]
  exact sum_congr rfl fun i _ => three_deg hG i c

lemma W3_univ (hU : UnanimousSP G) (c : ι → Fin 6) : W3 G univ c = 3 := by
  unfold W3
  have : (fun k => G (setS univ k c)) = top := by
    funext k
    unfold setS
    simp
    exact hU k
  rw [this]
  exact wind3_top

/-- With unanimity the degrees sum to 1. -/
theorem degree_sum (hG : SP G) (hU : UnanimousSP G) (c : ι → Fin 6) :
    ∑ i, degSP G i c = 1 := by
  have := lemma5_sum hG c
  rw [W3_univ hU] at this
  omega

/-! ### Proposition 3 and the Gibbard–Satterthwaite theorem -/

/-- **Proposition 3.** For three alternatives and any finite set of voters, a
    strategy-proof rule either gives every voter degree 0, or gives exactly
    one voter degree 1 and is that voter's dictatorship. -/
theorem prop3 (hG : SP G) :
    (∀ i c, degSP G i c = 0) ∨
      ∃ i, (∀ j c, degSP G j c = if j = i then 1 else 0) ∧ ∀ π, G π = top (π i) := by
  by_cases h : ∃ i c, degSP G i c ≠ 0
  · right
    obtain ⟨i, c, hic⟩ := h
    have hd1 : ∀ c', degSP G i c' = 1 := by
      intro c'
      rcases lemma6 hG i c' with h0 | h1
      · exact absurd ((lemma5 hG i c c').trans h0) hic
      · exact h1
    have hform : ∀ π, G π = top (π i) := by
      intro π
      have := top_of_deg hG i π (hd1 π) (π i)
      rwa [setS_self] at this
    refine ⟨i, fun j c' => ?_, hform⟩
    by_cases hji : j = i
    · rw [ite_eq_left hji, hji]
      exact hd1 c'
    · rw [ite_eq_right hji]
      have hconst : (fun k => G (setS {j} k c')) = fun _ => G c' := by
        funext k
        rw [hform, hform]
        unfold setS
        simp [Ne.symm hji]
      unfold degSP W3
      rw [hconst]
      simp [wind3, d3_self]
  · left
    push Not at h
    exact h

/-- **The Gibbard–Satterthwaite theorem for three alternatives, as a degree.**
    A strategy-proof rule with unanimity is a dictatorship. -/
theorem gs (hG : SP G) (hU : UnanimousSP G) : ∃ i, ∀ π, G π = top (π i) := by
  have hs := degree_sum hG hU (fun _ => 0)
  rcases prop3 hG with h0 | ⟨i, -, hform⟩
  · simp [h0] at hs
  · exact ⟨i, hform⟩

end GlobalFormSP

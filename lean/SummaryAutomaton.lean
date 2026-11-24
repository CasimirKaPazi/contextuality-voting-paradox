module

public import Mathlib

@[expose] public section

/-!
# The summary automaton for the rational diagonal

*The rational diagonal on totally tight game forms*, Section 3: the finite summary and its update
rule, which make the computer proof for totally tight forms with three and four outcomes a search
over summaries.

Setting. A game form `g : R → C → O`: rows `R` are the strategies of player i, columns `C` those
of the opponent, both finite and non-empty. Preferences are injective scores `u` (for i) and `v`
(for the opponent) on outcomes, larger is better.

* `IsY g r y`: `y` is the opponent's favourite outcome in row `r`.
* `colBest g c`: the best score for i in column `c`; `Mval g r y`: the best of these over the
  columns where `y` occurs in row `r`. The pair of row `r` is `(y, Mval g r y)`.
* `summary g`: the set of these pairs; `Works`: every pair has `u y < M`.

Results.
* `refuted_iff`: `u y < Mval g r y` exactly when among the opponent's best replies to `r` there is
  one whose column contains an outcome that i prefers to `y` (the definition of refutation).
* `works_iff`: player i works exactly when every row is refuted, so working depends only on the
  summary; `works_mono`: a larger summary makes working harder (monotonicity).
* `summary_addRow`: a new constant row with outcome `o` turns every `(y, M)` into
  `(y, M ⊔ u o)` and adds `(o, best ⊔ u o)`, where `best` is the best score for i in the form.
* `summary_addCol`: a new constant column with outcome `o` turns every `(y, M)` with
  `v y < v o` into `(o, u o)` and keeps the others.
-/

open Finset

namespace SummaryAutomaton

variable {O R C : Type*} [Fintype R] [Fintype C] [DecidableEq O]
variable (u v : O → ℕ)

/-- `y` is the opponent's favourite outcome in row `r`. -/
def IsY (g : R → C → O) (r : R) (y : O) : Prop := (∃ c, g r c = y) ∧ ∀ c, v (g r c) ≤ v y

/-- The best score for i in column `c`. -/
def colBest (g : R → C → O) (c : C) : ℕ := univ.sup (fun r => u (g r c))

/-- The best score for i over the columns in which `y` occurs in row `r`. -/
def Mval (g : R → C → O) (r : R) (y : O) : ℕ :=
  (univ.filter (fun c => g r c = y)).sup (colBest u g)

/-- The best score for i anywhere in the form. -/
def best (g : R → C → O) : ℕ := univ.sup (colBest u g)

/-- The summary: the pairs `(y, M)` of the rows. -/
def summary (g : R → C → O) : Set (O × ℕ) :=
  {p | ∃ r, IsY v g r p.1 ∧ p.2 = Mval u g r p.1}

/-- Player i works: every pair is refuted. -/
def Works (S : Set (O × ℕ)) : Prop := ∀ p ∈ S, u p.1 < p.2

/-! ### Basic facts -/

omit [Fintype R] [Fintype C] [DecidableEq O] in
lemma isY_unique {v : O → ℕ} (hv : Function.Injective v) {g : R → C → O} {r : R} {y y' : O}
    (h : IsY v g r y) (h' : IsY v g r y') : y = y' := by
  obtain ⟨⟨c, hc⟩, h1⟩ := h
  obtain ⟨⟨c', hc'⟩, h1'⟩ := h'
  apply hv
  have a := h1 c'
  have b := h1' c
  rw [hc'] at a
  rw [hc] at b
  omega

omit [Fintype R] [DecidableEq O] in
lemma exists_isY [Nonempty C] (g : R → C → O) (r : R) : ∃ y, IsY v g r y := by
  obtain ⟨c₀, -, hc₀⟩ := exists_max_image univ (fun c => v (g r c)) univ_nonempty
  exact ⟨g r c₀, ⟨c₀, rfl⟩, fun c => hc₀ c (mem_univ c)⟩

/-- Each column contains `y`, so `M` is at least as good as `y`. -/
lemma le_Mval {g : R → C → O} {r : R} {y : O} (h : ∃ c, g r c = y) : u y ≤ Mval u g r y := by
  obtain ⟨c, hc⟩ := h
  have h1 : u (g r c) ≤ colBest u g c := Finset.le_sup (f := fun r' => u (g r' c)) (mem_univ r)
  have h2 : colBest u g c ≤ Mval u g r y := by
    unfold Mval
    exact Finset.le_sup (f := colBest u g) (mem_filter.mpr ⟨mem_univ c, hc⟩)
  have h3 : u y = u (g r c) := by rw [hc]
  rw [h3]
  exact le_trans h1 h2

/-- The summary's test is the definition of refutation. -/
theorem refuted_iff (g : R → C → O) (r : R) (y : O) :
    u y < Mval u g r y ↔ ∃ c, g r c = y ∧ ∃ r', u y < u (g r' c) := by
  unfold Mval colBest
  rw [Finset.lt_sup_iff]
  constructor
  · rintro ⟨c, hc, h⟩
    rw [Finset.lt_sup_iff] at h
    obtain ⟨r', -, h'⟩ := h
    exact ⟨c, (mem_filter.mp hc).2, r', h'⟩
  · rintro ⟨c, hc, r', h⟩
    exact ⟨c, mem_filter.mpr ⟨mem_univ c, hc⟩,
      (Finset.lt_sup_iff).mpr ⟨r', mem_univ r', h⟩⟩

/-- Player i works exactly when every row is refuted. -/
theorem works_iff (g : R → C → O) :
    Works u (summary u v g) ↔ ∀ r y, IsY v g r y → u y < Mval u g r y := by
  constructor
  · intro h r y hy
    exact h (y, Mval u g r y) ⟨r, hy, rfl⟩
  · rintro h ⟨y, m⟩ ⟨r, hy, hm⟩
    simp only at hy hm ⊢
    rw [hm]
    exact h r y hy

omit [Fintype R] [Fintype C] [DecidableEq O] in
/-- Monotonicity: a summary with more pairs makes working harder. -/
theorem works_mono {S S' : Set (O × ℕ)} (hS : S ⊆ S') (h : Works u S') : Works u S :=
  fun p hp => h p (hS hp)

omit [Fintype R] [Fintype C] [DecidableEq O] in
lemma sup_sup_const {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℕ) (k : ℕ) :
    s.sup (fun c => f c ⊔ k) = s.sup f ⊔ k := by
  apply le_antisymm
  · exact Finset.sup_le (fun c hc => sup_le_sup_right (Finset.le_sup hc) k)
  · apply _root_.sup_le
    · exact Finset.sup_le (fun c hc =>
        le_trans le_sup_left (Finset.le_sup (f := fun c => f c ⊔ k) hc))
    · obtain ⟨c, hc⟩ := hs
      exact le_trans le_sup_right (Finset.le_sup (f := fun c => f c ⊔ k) hc)

/-! ### Adding a constant row of player i -/

/-- The form with a new row of i holding only `o`. -/
def addRow (g : R → C → O) (o : O) : Option R → C → O
  | none, _ => o
  | some r, c => g r c

omit [Fintype C] [DecidableEq O] in
lemma colBest_addRow (g : R → C → O) (o : O) (c : C) :
    colBest u (addRow g o) c = colBest u g c ⊔ u o := by
  apply le_antisymm
  · apply Finset.sup_le
    intro r' _
    cases r' with
    | none => exact le_sup_right
    | some r =>
      exact le_trans (Finset.le_sup (f := fun r => u (g r c)) (mem_univ r)) le_sup_left
  · apply _root_.sup_le
    · apply Finset.sup_le
      intro r _
      exact Finset.le_sup (f := fun r' => u (addRow g o r' c)) (mem_univ (some r))
    · exact Finset.le_sup (f := fun r' => u (addRow g o r' c)) (mem_univ none)

lemma Mval_addRow_some (g : R → C → O) (o : O) {r : R} {y : O} (h : ∃ c, g r c = y) :
    Mval u (addRow g o) (some r) y = Mval u g r y ⊔ u o := by
  have hne : (univ.filter (fun c => g r c = y)).Nonempty := by
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by simp [hc]⟩
  unfold Mval
  have e : (univ.filter (fun c => addRow g o (some r) c = y)) =
      univ.filter (fun c => g r c = y) := rfl
  have hcb : colBest u (addRow g o) = fun c => colBest u g c ⊔ u o :=
    funext (colBest_addRow u g o)
  rw [e, hcb, sup_sup_const hne]

lemma Mval_addRow_none [Nonempty C] (g : R → C → O) (o : O) :
    Mval u (addRow g o) none o = best u g ⊔ u o := by
  unfold Mval best
  have e : (univ.filter (fun c => addRow g o none c = o)) = univ := by
    ext c; simp [addRow]
  have hcb : colBest u (addRow g o) = fun c => colBest u g c ⊔ u o :=
    funext (colBest_addRow u g o)
  rw [e, hcb, sup_sup_const univ_nonempty]

omit [Fintype R] [Fintype C] [DecidableEq O] in
lemma isY_addRow_none [Nonempty C] {g : R → C → O} {o y : O} :
    IsY v (addRow g o) none y ↔ y = o := by
  constructor
  · rintro ⟨⟨c, hc⟩, -⟩
    exact hc.symm
  · rintro rfl
    obtain ⟨c⟩ := ‹Nonempty C›
    exact ⟨⟨c, rfl⟩, fun _ => le_rfl⟩

/-- Update rule for a new constant row of player i. -/
theorem summary_addRow [Nonempty C] (g : R → C → O) (o : O) :
    summary u v (addRow g o) =
      (fun p => (p.1, p.2 ⊔ u o)) '' summary u v g ∪ {(o, best u g ⊔ u o)} := by
  ext ⟨y, m⟩
  simp only [summary, Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    Prod.mk.injEq]
  constructor
  · rintro ⟨r', hy, hm⟩
    cases r' with
    | none =>
      have hyo : y = o := (isY_addRow_none v).mp hy
      right
      subst hyo
      exact ⟨rfl, by rw [hm, Mval_addRow_none]⟩
    | some r =>
      have hy' : IsY v g r y := hy
      left
      refine ⟨(y, Mval u g r y), ⟨r, hy', rfl⟩, rfl, ?_⟩
      rw [hm, Mval_addRow_some u g o hy'.1]
  · rintro (⟨⟨y₀, m₀⟩, ⟨r, hy₀, hm₀⟩, h1, h2⟩ | ⟨h1, h2⟩)
    · simp only at hy₀ hm₀ h1 h2
      subst h1
      refine ⟨some r, hy₀, ?_⟩
      rw [← h2, hm₀, Mval_addRow_some u g o hy₀.1]
    · subst h1
      refine ⟨none, (isY_addRow_none v).mpr rfl, ?_⟩
      rw [h2, Mval_addRow_none]

/-! ### Adding a constant column of the opponent -/

/-- The form with a new column of the opponent holding only `o`. -/
def addCol (g : R → C → O) (o : O) : R → Option C → O
  | _, none => o
  | r, some c => g r c

omit [Fintype C] [DecidableEq O] in
lemma colBest_addCol_some (g : R → C → O) (o : O) (c : C) :
    colBest u (addCol g o) (some c) = colBest u g c := rfl

omit [Fintype C] [DecidableEq O] in
lemma colBest_addCol_none [Nonempty R] (g : R → C → O) (o : O) :
    colBest u (addCol g o) none = u o := by
  unfold colBest
  exact Finset.sup_const (univ_nonempty (α := R)) (u o)

/-- Rows whose favourite the opponent ranks below `o` become `(o, u o)`. -/
lemma addCol_dominated [Nonempty R] {g : R → C → O} {o : O} {r : R} {y : O}
    (hy : IsY v g r y) (hlt : v y < v o) :
    IsY v (addCol g o) r o ∧ Mval u (addCol g o) r o = u o := by
  refine ⟨⟨⟨none, rfl⟩, fun c' => ?_⟩, ?_⟩
  · cases c' with
    | none => exact le_rfl
    | some c => exact le_trans (hy.2 c) hlt.le
  · have e : (univ.filter (fun c' => addCol g o r c' = o)) = {none} := by
      ext c'
      cases c' with
      | none =>
        exact ⟨fun _ => mem_singleton_self _, fun _ => mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
      | some c =>
        simp only [mem_filter, mem_univ, true_and, mem_singleton, reduceCtorEq, iff_false]
        intro hc
        have := hy.2 c
        change g r c = o at hc
        rw [hc] at this
        omega
    unfold Mval
    rw [e, sup_singleton, colBest_addCol_none]

/-- The other rows keep their pair. -/
lemma addCol_kept {g : R → C → O} {o : O} {r : R} {y : O}
    (hy : IsY v g r y) (hle : ¬ v y < v o) :
    IsY v (addCol g o) r y ∧ Mval u (addCol g o) r y = Mval u g r y := by
  refine ⟨⟨?_, fun c' => ?_⟩, ?_⟩
  · obtain ⟨c, hc⟩ := hy.1
    exact ⟨some c, hc⟩
  · cases c' with
    | none => exact not_lt.mp hle
    | some c => exact hy.2 c
  · have hyM := le_Mval u hy.1
    unfold Mval at hyM ⊢
    apply le_antisymm
    · apply Finset.sup_le
      intro c' hc'
      rw [mem_filter] at hc'
      cases c' with
      | none =>
        have hoy : o = y := hc'.2
        have hcb : colBest u (addCol g o) none ≤ u o := by
          unfold colBest
          exact Finset.sup_le (fun _ _ => le_rfl)
        calc colBest u (addCol g o) none ≤ u o := hcb
          _ = u y := by rw [hoy]
          _ ≤ _ := hyM
      | some c =>
        rw [colBest_addCol_some]
        exact Finset.le_sup (f := colBest u g) (mem_filter.mpr ⟨mem_univ c, hc'.2⟩)
    · apply Finset.sup_le
      intro c hc
      rw [← colBest_addCol_some u g o c]
      exact Finset.le_sup (f := colBest u (addCol g o))
        (mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hc).2⟩)

/-- Update rule for a new constant column of the opponent. -/
theorem summary_addCol [Nonempty R] [Nonempty C] (hv : Function.Injective v)
    (g : R → C → O) (o : O) :
    summary u v (addCol g o) =
      (fun p => if v p.1 < v o then (o, u o) else p) '' summary u v g := by
  ext ⟨y', m'⟩
  simp only [summary, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨r, hy', hm'⟩
    obtain ⟨y, hy⟩ := exists_isY v g r
    refine ⟨(y, Mval u g r y), ⟨r, hy, rfl⟩, ?_⟩
    by_cases hlt : v y < v o
    · obtain ⟨h1, h2⟩ := addCol_dominated u v hy hlt
      have e := isY_unique hv hy' h1
      simp only [hlt, ↓reduceIte, Prod.mk.injEq]
      exact ⟨e.symm, by rw [hm', e, h2]⟩
    · obtain ⟨h1, h2⟩ := addCol_kept u v hy hlt
      have e := isY_unique hv hy' h1
      simp only [hlt, ↓reduceIte, Prod.mk.injEq]
      exact ⟨e.symm, by rw [hm', e, h2]⟩
  · rintro ⟨⟨y, m⟩, ⟨r, hy, hm⟩, hp⟩
    simp only at hy hm
    by_cases hlt : v y < v o
    · obtain ⟨h1, h2⟩ := addCol_dominated u v hy hlt
      simp only [hlt, ↓reduceIte, Prod.mk.injEq] at hp
      obtain ⟨e1, e2⟩ := hp
      subst e1 e2
      exact ⟨r, h1, h2.symm⟩
    · obtain ⟨h1, h2⟩ := addCol_kept u v hy hlt
      simp only [hlt, ↓reduceIte, Prod.mk.injEq] at hp
      obtain ⟨e1, e2⟩ := hp
      subst e1 e2
      exact ⟨r, h1, by rw [h2, hm]⟩

end SummaryAutomaton

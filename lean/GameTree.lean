/-
  Games of perfect information have the recombination property (R) of
  *The rational diagonal on totally tight game forms*
  (`notes/rational-diagonal-totally-tight.md`, Section 7), and so, by
  `TotallyTight.three_outcomes`, every non-dictatorial game of perfect
  information with three outcomes, all occurring, admits a rational diagonal
  for some player.

  Setting.
  * `Tree X`: a finite game tree with outcomes in `X` at the leaves. At a node
    the owner (`false` for player 1, `true` for player 2) chooses one of
    `n + 1` children; any number of branches is allowed.
  * A position is the list of moves made so far, the most recent first. A
    plan (`Plan`) chooses a number at every position; at a node with `n + 1`
    children it is read modulo `n + 1` (`pick`). So every plan of the game
    tree is represented, many of them more than once, and the normal form
    `nf T` (rows: player 1's plans, columns: player 2's) is the usual one with
    repeated lines.
  * `play T q r s`: the outcome reached from position `q` of the subtree `T`.

  Results.
  * `play_congr`: the outcome from `q` depends only on what the two plans
    choose at positions below `q` (lists with `q` as a suffix).
  * `recomb_play`, `recomb`: the normal form of every tree has (R). For two
    cells x = (r, s₀) and y = (r₀, s), follow both plays from the root. Where
    they reach the same child, recurse, patching the choice at the current
    node if needed. At the first node where they part, the owner's opponent
    is not involved there: if the node is player 1's, the column that plays
    s₀ below the branch of x and s elsewhere (`splice`) gives x's outcome
    against r and y's against r₀; if it is player 2's, the same with rows.
  * `three_outcomes_tree`: the theorem for three outcomes on trees.

  Not here: the reduction to seven outcomes and the search over trees for
  more outcomes (Proposition 5′ of *Walls and Strategy*); that removing
  repeated lines changes neither (R) nor the rational diagonal.
-/

module

public import Mathlib
public import TotallyTight

@[expose] public section

namespace GameTree

open NonTight TwoPlayer TotallyTight

/-- A finite two-player game tree with outcomes at the leaves. At a node the
    owner (`false`: player 1, `true`: player 2) chooses one of `n + 1`
    children. -/
inductive Tree (X : Type) where
  | leaf : X → Tree X
  | node : Bool → (n : ℕ) → (Fin (n + 1) → Tree X) → Tree X

/-- A plan: a choice at every position. Positions are lists of moves, most
    recent first. -/
abbrev Plan := List ℕ → ℕ

variable {X : Type}

/-- A choice read at a node with `n + 1` children. -/
def pick (n k : ℕ) : Fin (n + 1) := ⟨k % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

/-- The outcome reached from position `q` of the subtree, under plans `r` of
    player 1 and `s` of player 2. -/
def play : Tree X → List ℕ → Plan → Plan → X
  | .leaf x, _, _, _ => x
  | .node false n ch, q, r, s => play (ch (pick n (r q))) ((pick n (r q)).val :: q) r s
  | .node true n ch, q, r, s => play (ch (pick n (s q))) ((pick n (s q)).val :: q) r s

/-- The normal form of a tree: rows are player 1's plans, columns player 2's. -/
def nf (T : Tree X) : Plan → Plan → X := fun r s => play T [] r s

lemma play_leaf (x : X) (q : List ℕ) (r s : Plan) : play (.leaf x) q r s = x := by
  simp only [play]

lemma play_node1 (n : ℕ) (ch : Fin (n + 1) → Tree X) (q : List ℕ) (r s : Plan) :
    play (.node false n ch) q r s = play (ch (pick n (r q))) ((pick n (r q)).val :: q) r s := by
  simp only [play]

lemma play_node2 (n : ℕ) (ch : Fin (n + 1) → Tree X) (q : List ℕ) (r s : Plan) :
    play (.node true n ch) q r s = play (ch (pick n (s q))) ((pick n (s q)).val :: q) r s := by
  simp only [play]

/-- The outcome from `q` depends only on the choices at positions below `q`. -/
theorem play_congr (T : Tree X) : ∀ (q : List ℕ) (r r' s s' : Plan),
    (∀ l, q <:+ l → r l = r' l) → (∀ l, q <:+ l → s l = s' l) →
    play T q r s = play T q r' s' := by
  induction T with
  | leaf x => intro q r r' s s' _ _; rw [play_leaf, play_leaf]
  | node p n ch ih =>
    intro q r r' s s' hr hs
    have hr' : ∀ i : ℕ, ∀ l, (i :: q) <:+ l → r l = r' l :=
      fun i l hl => hr l ((List.suffix_cons i q).trans hl)
    have hs' : ∀ i : ℕ, ∀ l, (i :: q) <:+ l → s l = s' l :=
      fun i l hl => hs l ((List.suffix_cons i q).trans hl)
    cases p
    · rw [play_node1, play_node1, hr q (List.suffix_refl q)]
      exact ih _ _ r r' s s' (hr' _) (hs' _)
    · rw [play_node2, play_node2, hs q (List.suffix_refl q)]
      exact ih _ _ r r' s s' (hr' _) (hs' _)

/-! ### Changing a plan at one position or below one branch -/

lemma suffix_eq {a b l : List ℕ} (ha : a <:+ l) (hb : b <:+ l) (h : a.length = b.length) :
    a = b := by
  obtain ⟨t₁, rfl⟩ := ha
  obtain ⟨t₂, e⟩ := hb
  have hl : t₂.length = t₁.length := by
    have := congrArg List.length e
    simp only [List.length_append] at this
    omega
  exact (List.append_inj e hl).2.symm

/-- Below one branch, a position is not below another branch of the same node. -/
lemma not_suffix_of_ne {i j : ℕ} {q l : List ℕ} (hij : i ≠ j) (hj : (j :: q) <:+ l) :
    ¬ (i :: q) <:+ l := fun hi =>
  hij (List.cons.inj (suffix_eq hi hj (by simp only [List.length_cons]))).1

open Classical in
/-- The plan `t` with the choice `c` at position `q`. -/
noncomputable def patch (q : List ℕ) (c : ℕ) (t : Plan) : Plan := fun l => if l = q then c else t l

lemma patch_at (q : List ℕ) (c : ℕ) (t : Plan) : patch q c t q = c := by
  unfold patch
  exact ite_eq_left rfl

lemma patch_below {q l : List ℕ} {i c : ℕ} {t : Plan} (h : (i :: q) <:+ l) :
    patch q c t l = t l := by
  unfold patch
  refine ite_eq_right ?_
  rintro rfl
  have := h.length_le
  simp only [List.length_cons] at this
  omega

open Classical in
/-- The plan `t₁` at positions below `q` and `t₂` elsewhere. -/
noncomputable def splice (q : List ℕ) (t₁ t₂ : Plan) : Plan := fun l => if q <:+ l then t₁ l else t₂ l

lemma splice_in {q l : List ℕ} {t₁ t₂ : Plan} (h : q <:+ l) : splice q t₁ t₂ l = t₁ l := by
  unfold splice
  exact ite_eq_left h

lemma splice_out {q l : List ℕ} {t₁ t₂ : Plan} (h : ¬ q <:+ l) : splice q t₁ t₂ l = t₂ l := by
  unfold splice
  exact ite_eq_right h

/-! ### Recombination -/

/-- (R) from every position of every tree. -/
theorem recomb_play (T : Tree X) : ∀ (q : List ℕ) (r s₀ r₀ s : Plan),
    (∃ r', play T q r' s₀ = play T q r s₀ ∧ play T q r' s = play T q r₀ s) ∨
    (∃ s', play T q r s' = play T q r s₀ ∧ play T q r₀ s' = play T q r₀ s) := by
  induction T with
  | leaf x => intro q r s₀ r₀ s; exact Or.inl ⟨r, rfl, by rw [play_leaf, play_leaf]⟩
  | node p n ch ih =>
    intro q r s₀ r₀ s
    cases p
    · -- player 1 moves: x follows r, y follows r₀
      by_cases hij : pick n (r q) = pick n (r₀ q)
      · rcases ih (pick n (r q)) ((pick n (r q)).val :: q) r s₀ r₀ s with
          ⟨r', h1, h2⟩ | ⟨s', h1, h2⟩
        · refine Or.inl ⟨patch q (r q) r', ?_, ?_⟩
          · rw [play_node1, play_node1, patch_at]
            refine Eq.trans (play_congr _ _ _ r' _ s₀ ?_ ?_) h1
            · intro l hl; exact patch_below hl
            · intro _ _; rfl
          · rw [play_node1, play_node1, patch_at, ← hij]
            refine Eq.trans (play_congr _ _ _ r' _ s ?_ ?_) h2
            · intro l hl; exact patch_below hl
            · intro _ _; rfl
        · refine Or.inr ⟨s', ?_, ?_⟩
          · rw [play_node1, play_node1]
            exact h1
          · rw [play_node1, play_node1, ← hij]
            exact h2
      · refine Or.inr ⟨splice ((pick n (r q)).val :: q) s₀ s, ?_, ?_⟩
        · rw [play_node1, play_node1]
          exact play_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun l hl => splice_in hl)
        · rw [play_node1, play_node1]
          exact play_congr _ _ _ _ _ _ (fun _ _ => rfl)
            (fun l hl => splice_out (not_suffix_of_ne (fun e => hij (Fin.ext e)) hl))
    · -- player 2 moves: x follows s₀, y follows s
      by_cases hij : pick n (s₀ q) = pick n (s q)
      · rcases ih (pick n (s₀ q)) ((pick n (s₀ q)).val :: q) r s₀ r₀ s with
          ⟨r', h1, h2⟩ | ⟨s', h1, h2⟩
        · refine Or.inl ⟨r', ?_, ?_⟩
          · rw [play_node2, play_node2]
            exact h1
          · rw [play_node2, play_node2, ← hij]
            exact h2
        · refine Or.inr ⟨patch q (s₀ q) s', ?_, ?_⟩
          · rw [play_node2, play_node2, patch_at]
            refine Eq.trans (play_congr _ _ _ r _ s' ?_ ?_) h1
            · intro _ _; rfl
            · intro l hl; exact patch_below hl
          · rw [play_node2, play_node2, patch_at, ← hij]
            refine Eq.trans (play_congr _ _ _ r₀ _ s' ?_ ?_) h2
            · intro _ _; rfl
            · intro l hl; exact patch_below hl
      · refine Or.inl ⟨splice ((pick n (s₀ q)).val :: q) r r₀, ?_, ?_⟩
        · rw [play_node2, play_node2]
          exact play_congr _ _ _ _ _ _ (fun l hl => splice_in hl) (fun _ _ => rfl)
        · rw [play_node2, play_node2]
          exact play_congr _ _ _ _ _ _
            (fun l hl => splice_out (not_suffix_of_ne (fun e => hij (Fin.ext e)) hl))
            (fun _ _ => rfl)

/-- **Games of perfect information have (R).** -/
theorem recomb (T : Tree X) : Recomb (nf T) :=
  fun r s₀ r₀ s => recomb_play T [] r s₀ r₀ s

/-- **Three outcomes on trees.** Every non-dictatorial game of perfect
    information with three outcomes, all occurring, admits a rational diagonal
    for some player. -/
theorem three_outcomes_tree [DecidableEq X] (T : Tree X) {a b c : X} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hcov : ∀ x, x = a ∨ x = b ∨ x = c) (honto : ∀ x, ∃ r s, nf T r s = x)
    (hnd1 : ¬ ∀ x, ∃ r, ∀ s, nf T r s = x) (hnd2 : ¬ ∀ x, ∃ s, ∀ r, nf T r s = x) :
    RationalDiagonal1 (nf T) ∨ RationalDiagonal2 (nf T) :=
  TotallyTight.three_outcomes (recomb T) hab hac hbc hcov honto hnd1 hnd2

end GameTree

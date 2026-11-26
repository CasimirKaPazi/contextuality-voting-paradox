/-
  The corollary of Section 6 of *What Cannot Be Defined from Inside*
  (`notes/alignment/undefinability.md`): revising the rule does not escape
  the dichotomy of Theorem 3 (`Dichotomy.dichotomy`).

  A procedure built by composition (`Proc`) is either a game form (a leaf), or
  a game form h whose outcome j selects the procedure to play next (a node),
  each participant seeing j. A strategy in a node is a strategy for h together
  with a strategy for every procedure h may select, a contingency plan
  (`Proc.St`). The procedure then assigns an outcome to every profile of
  strategies (`Proc.play`), so it is again a game form in Gibbard's sense, and
  Theorem 3 applies to it (`composite_dichotomy`). Nodes may be nested to any
  finite depth, and h itself may be the play of a procedure, so this covers
  every finite composition. The one-step composite of the note is `compose`.

  Gibbard's outcomes are the range of the game form. The corollary assumes
  only that the composite reaches three distinct outcomes, among finitely many
  possible ones; `GameForm.ofRange` turns any such function into a game form
  on its range (`Range`). Dictatorship on the range is the usual notion
  (`isDictator_toRange`): some participant can force every reachable outcome.

  As in `Gibbard73.lean`, all participants draw strategies from one type at
  each node; different strategy sets are covered by taking their union.
-/

module

public import Dichotomy

@[expose] public section

namespace Composition

open Arrow Gibbard73

/-! ### Procedures built by composition -/

/-- A leaf is a game form with strategies in `St`. A node plays the game form
    `h`; its outcome `j` selects the procedure `next j` played afterwards. -/
inductive Proc (I X : Type) : Type 1 where
  | leaf (St : Type) (g : (I → St) → X)
  | node (Sh J : Type) (h : (I → Sh) → J) (next : J → Proc I X)

namespace Proc

variable {I X : Type}

/-- Strategies: in a node, a strategy for h and a contingency plan, one
    strategy for each procedure h may select. -/
def St : Proc I X → Type
  | leaf S _ => S
  | node Sh J _ next => Sh × ((j : J) → St (next j))

/-- The outcome of a profile of strategies: play h, then the selected
    procedure with the plans for it. -/
def play : (p : Proc I X) → (I → p.St) → X
  | leaf _ g, s => g s
  | node _ _ h next, s =>
      play (next (h fun i => Prod.fst (s i))) fun i => Prod.snd (s i) (h fun i => Prod.fst (s i))

end Proc

/-- The composite of the note: play h, then the form g j that h selects. -/
def compose {I X Sh J : Type} (h : (I → Sh) → J) (Sg : J → Type)
    (g : (j : J) → (I → Sg j) → X) : Proc I X :=
  .node Sh J h fun j => .leaf (Sg j) (g j)

theorem play_compose {I X Sh J : Type} (h : (I → Sh) → J) (Sg : J → Type)
    (g : (j : J) → (I → Sg j) → X) (s : I → Sh × ((j : J) → Sg j)) :
    (compose h Sg g).play s = g (h fun i => (s i).1) fun i => (s i).2 (h fun i => (s i).1) :=
  rfl

/-! ### Outcomes as the range -/

section Range

variable {X I St : Type}

/-- The outcomes that g reaches. -/
abbrev Range (g : (I → St) → X) : Type := {x : X // ∃ s, g s = x}

/-- g with values in its range. -/
def toRange (g : (I → St) → X) : (I → St) → Range g := fun s => ⟨g s, s, rfl⟩

open Classical in
/-- The reachable outcomes among a list of all outcomes. -/
noncomputable def rangeList (g : (I → St) → X) (allX : List X) : List (Range g) :=
  allX.filterMap fun x => if h : ∃ s, g s = x then some ⟨x, h⟩ else none

theorem mem_rangeList (g : (I → St) → X) {allX : List X} (hallX : ∀ x, x ∈ allX)
    (y : Range g) : y ∈ rangeList g allX := by
  obtain ⟨x, hx⟩ := y
  exact List.mem_filterMap.mpr ⟨x, hallX x, dite_eq_left hx⟩

/-- A function on profiles with finitely many possible values and three
    distinct reached ones is a game form on its range. -/
noncomputable def GameForm.ofRange (g : (I → St) → X) (allX : List X)
    (hallX : ∀ x, x ∈ allX) (allI : List I) (hallI : ∀ i, i ∈ allI) (s₁ s₂ s₃ : I → St)
    (h₁₂ : g s₁ ≠ g s₂) (h₁₃ : g s₁ ≠ g s₃) (h₂₃ : g s₂ ≠ g s₃) :
    GameForm (Range g) I St where
  allX := rangeList g allX
  hallX := mem_rangeList g hallX
  allI := allI
  hallI := hallI
  g := toRange g
  onto := fun y => by
    obtain ⟨x, s, hs⟩ := y
    exact ⟨s, Subtype.ext hs⟩
  a := toRange g s₁
  b := toRange g s₂
  c := toRange g s₃
  hab := fun h => h₁₂ (congrArg Subtype.val h)
  hac := fun h => h₁₃ (congrArg Subtype.val h)
  hbc := fun h => h₂₃ (congrArg Subtype.val h)

end Range

/-! ### The dichotomy for composite procedures -/

section Dichotomy

variable {X I St : Type} [DecidableEq X] [DecidableEq I]

omit [DecidableEq X] [DecidableEq I] in
/-- Dictatorship on the range: k can force every reachable outcome. -/
theorem isDictator_toRange (g : (I → St) → X) (k : I) :
    IsDictator (toRange g) k ↔ ∀ s₀ : I → St, ∃ t : St, ∀ s, s k = t → g s = g s₀ := by
  constructor
  · intro h s₀
    obtain ⟨t, ht⟩ := h (toRange g s₀)
    exact ⟨t, fun s hs => congrArg Subtype.val (ht s hs)⟩
  · intro h y
    obtain ⟨x, s₀, rfl⟩ := y
    obtain ⟨t, ht⟩ := h s₀
    exact ⟨t, fun s hs => Subtype.ext (ht s hs)⟩

/-- Theorem 3 for any function on profiles that reaches three distinct
    outcomes among finitely many: it is dictatorial on its range, or some
    player at some ordering of the reachable outcomes has no universally
    correct strategist against opponents able to simulate it. -/
theorem dichotomy_range (g : (I → St) → X) (allX : List X) (hallX : ∀ x, x ∈ allX)
    (allI : List I) (hallI : ∀ i, i ∈ allI) (s₁ s₂ s₃ : I → St)
    (h₁₂ : g s₁ ≠ g s₂) (h₁₃ : g s₁ ≠ g s₃) (h₂₃ : g s₂ ≠ g s₃)
    (hnd : ∀ k, ¬ ∀ s₀ : I → St, ∃ t : St, ∀ s, s k = t → g s = g s₀) :
    ∃ (k : I) (P : Rel (Range g)), IsOrdering P ∧
      ∀ (Env : Type) (M : Env → Option St) (opp : Env → Option (I → St)),
        Diagonal.CanSimulate M opp →
        ¬ Diagonal.UniversallyCorrect (fun b r => toRange g (upd r k b))
            (fun o o' => P o' o = false) M opp :=
  Dichotomy.dichotomy (GameForm.ofRange g allX hallX allI hallI s₁ s₂ s₃ h₁₂ h₁₃ h₂₃)
    fun k hk => hnd k ((isDictator_toRange g k).mp hk)

/-- The corollary of *What Cannot Be Defined from Inside*, Section 6: a
    procedure built by composition, to any finite depth, that can reach three
    distinct outcomes is dictatorial, or some participant at some preference
    has no universally correct strategist. -/
theorem composite_dichotomy (p : Proc I X) (allX : List X) (hallX : ∀ x, x ∈ allX)
    (allI : List I) (hallI : ∀ i, i ∈ allI) (s₁ s₂ s₃ : I → p.St)
    (h₁₂ : p.play s₁ ≠ p.play s₂) (h₁₃ : p.play s₁ ≠ p.play s₃)
    (h₂₃ : p.play s₂ ≠ p.play s₃)
    (hnd : ∀ k, ¬ ∀ s₀ : I → p.St, ∃ t : p.St, ∀ s, s k = t → p.play s = p.play s₀) :
    ∃ (k : I) (P : Rel (Range p.play)), IsOrdering P ∧
      ∀ (Env : Type) (M : Env → Option p.St) (opp : Env → Option (I → p.St)),
        Diagonal.CanSimulate M opp →
        ¬ Diagonal.UniversallyCorrect (fun b r => toRange p.play (upd r k b))
            (fun o o' => P o' o = false) M opp :=
  dichotomy_range p.play allX hallX allI hallI s₁ s₂ s₃ h₁₂ h₁₃ h₂₃ hnd

end Dichotomy

end Composition

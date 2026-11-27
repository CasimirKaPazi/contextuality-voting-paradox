/-
  One frame for two-player game forms (roadmap, item 1.1).

  A two-player game form is a function g : A → B → X: rows for player 1,
  columns for player 2, outcomes X. Strict preferences are injective utilities
  in ℕ, higher is better. The basic notions are those of `NonTight.lean`:
  best replies `BR1`, `BR2`, forcing, tightness and the rational diagonal for
  player 1, `RationalDiagonal1`. This file adds what the later results share:

  * player 2's side: `RationalDiagonal2`, and strict Nash strategies for both
    players (`StrictNash1`, `StrictNash2`); a player has no rational diagonal
    exactly when it has a strict Nash strategy under every pair of strict
    preferences (`not_rd1_iff`, `not_rd2_iff`);
  * the transpose, which exchanges the players (`transpose`, `rd2_iff`,
    `strictNash2_iff`, `tight_transpose`), so that every statement for
    player 1 gives one for player 2;
  * best replies depend only on the order of the utilities (`br1_congr`,
    `br2_congr`), and a common veto gives tightness (`tight_of_common_veto`);
  * the bridge to `SummaryAutomaton.lean`, whose `Works` is stated through
    the summary of rows: for an injective opponent utility, player 1 works
    exactly when against every row some best reply of player 2 makes the row
    not a best reply (`works_iff_br`), so the rational diagonal of
    `NonTight.lean` is the existence of a working pair of strict preferences
    (`rd1_iff_works`).

  The general part moves here from `TightCounterexample.lean`, which now uses
  it. Not bridged: `RationalDiagonal.lean`, whose certificates are stated for
  voting rules on lists of rankings, and `Gibbard73.lean`, whose game forms
  have n players and no rational diagonal.
-/

module

public import Mathlib
public import NonTight
public import SummaryAutomaton

@[expose] public section

namespace TwoPlayer

open NonTight

section General

variable {A B X : Type}

lemma injective_iff (f : X → Nat) : Injective f ↔ Function.Injective f :=
  ⟨fun h a b => h a b, fun h a b => @h a b⟩

/-! ### Strict Nash strategies and the rational diagonal -/

/-- Row a is a strict Nash strategy of player 1: a best reply to every best
    reply of player 2. -/
def StrictNash1 (g : A → B → X) (u v : X → Nat) (a : A) : Prop :=
  ∀ b, BR2 g v a b → BR1 g u a b

/-- Column b is a strict Nash strategy of player 2. -/
def StrictNash2 (g : A → B → X) (u v : X → Nat) (b : B) : Prop :=
  ∀ a, BR1 g u a b → BR2 g v a b

/-- Rational diagonal for player 2: strict preferences such that against every
    column some best reply of player 1 makes that column not a best reply. -/
def RationalDiagonal2 (g : A → B → X) : Prop :=
  ∃ u v : X → Nat, Injective u ∧ Injective v ∧ ∀ b, ∃ a, BR1 g u a b ∧ ¬ BR2 g v a b

/-- Player 1 has no rational diagonal exactly when, under every pair of strict
    preferences, it has a strict Nash strategy. -/
theorem not_rd1_iff (g : A → B → X) :
    ¬ RationalDiagonal1 g ↔
      ∀ u v : X → Nat, Injective u → Injective v → ∃ a, StrictNash1 g u v a := by
  unfold RationalDiagonal1 StrictNash1
  constructor
  · intro h u v hu hv
    by_contra hc
    push Not at hc
    exact h ⟨u, v, hu, hv, hc⟩
  · rintro h ⟨u, v, hu, hv, hd⟩
    obtain ⟨a, ha⟩ := h u v hu hv
    obtain ⟨b, hb2, hb1⟩ := hd a
    exact hb1 (ha b hb2)

/-! ### Exchanging the players -/

/-- The transpose: player 2's strategies become the rows. -/
def transpose (g : A → B → X) : B → A → X := fun b a => g a b

theorem br1_transpose (g : A → B → X) (v : X → Nat) (a : A) (b : B) :
    BR1 (transpose g) v b a ↔ BR2 g v a b := Iff.rfl

theorem br2_transpose (g : A → B → X) (u : X → Nat) (a : A) (b : B) :
    BR2 (transpose g) u b a ↔ BR1 g u a b := Iff.rfl

theorem strictNash2_iff (g : A → B → X) (u v : X → Nat) (b : B) :
    StrictNash2 g u v b ↔ StrictNash1 (transpose g) v u b := Iff.rfl

/-- Player 2's rational diagonal is player 1's in the transpose. -/
theorem rd2_iff (g : A → B → X) : RationalDiagonal2 g ↔ RationalDiagonal1 (transpose g) :=
  ⟨fun ⟨u, v, hu, hv, h⟩ => ⟨v, u, hv, hu, h⟩, fun ⟨v, u, hv, hu, h⟩ => ⟨u, v, hu, hv, h⟩⟩

theorem not_rd2_iff (g : A → B → X) :
    ¬ RationalDiagonal2 g ↔
      ∀ u v : X → Nat, Injective u → Injective v → ∃ b, StrictNash2 g u v b := by
  rw [rd2_iff, not_rd1_iff]
  exact ⟨fun h u v hu hv => h v u hv hu, fun h v u hv hu => h u v hu hv⟩

/-- Tightness is symmetric in the players. -/
theorem tight_transpose {g : A → B → X} (h : Tight g) : Tight (transpose g) := by
  intro S
  rcases h (fun x => !S x) with ⟨a, ha⟩ | ⟨b, hb⟩
  · exact Or.inr ⟨a, fun b => ha b⟩
  · exact Or.inl ⟨b, fun a => by simpa [transpose] using hb a⟩

/-! ### Order, and the common veto -/

/-- Best replies depend only on the order of the utilities. -/
theorem br1_congr (g : A → B → X) {u w : X → Nat} (h : ∀ x y, u x ≤ u y ↔ w x ≤ w y)
    (a : A) (b : B) : BR1 g u a b ↔ BR1 g w a b :=
  forall_congr' fun _ => h _ _

theorem br2_congr (g : A → B → X) {v w : X → Nat} (h : ∀ x y, v x ≤ v y ↔ w x ≤ w y)
    (a : A) (b : B) : BR2 g v a b ↔ BR2 g w a b :=
  forall_congr' fun _ => h _ _

/-- A common veto: an outcome x that player 1 forces with a row and player 2
    with a column. Every form with a common veto is tight, since every set of
    outcomes or its complement contains x. -/
theorem tight_of_common_veto (g : A → B → X) (x : X) (r : A) (hr : ∀ s, g r s = x)
    (s : B) (hs : ∀ r, g r s = x) : Tight g := by
  intro S
  cases h : S x with
  | true => exact Or.inl ⟨r, fun b => by simp [hr b, h]⟩
  | false => exact Or.inr ⟨s, fun a => by simp [hs a, h]⟩

end General

/-! ### The bridge to the summary automaton -/

section Summary

variable {A B X : Type} [Fintype A] [Fintype B] [DecidableEq X]

/-- For an injective opponent utility, `Works` of `SummaryAutomaton.lean` says
    that against every row some best reply of player 2 makes the row not a
    best reply of player 1. -/
theorem works_iff_br [Nonempty B] {u v : X → ℕ} (hv : Function.Injective v) (g : A → B → X) :
    SummaryAutomaton.Works u (SummaryAutomaton.summary u v g) ↔
      ∀ a, ∃ b, BR2 g v a b ∧ ¬ BR1 g u a b := by
  rw [SummaryAutomaton.works_iff]
  constructor
  · intro h a
    obtain ⟨y, hy⟩ := SummaryAutomaton.exists_isY v g a
    obtain ⟨b, hb, a', ha'⟩ := (SummaryAutomaton.refuted_iff u g a y).mp (h a y hy)
    refine ⟨b, fun b' => ?_, fun h1 => ?_⟩
    · rw [hb]
      exact hy.2 b'
    · have := h1 a'
      rw [hb] at this
      omega
  · intro h a y hy
    obtain ⟨b, hb2, hb1⟩ := h a
    rw [SummaryAutomaton.refuted_iff]
    obtain ⟨⟨c, hc⟩, hmax⟩ := hy
    have hby : g a b = y := by
      apply hv
      apply le_antisymm (hmax b)
      have := hb2 c
      rw [hc] at this
      exact this
    refine ⟨b, hby, ?_⟩
    unfold BR1 at hb1
    push Not at hb1
    obtain ⟨a', ha'⟩ := hb1
    exact ⟨a', by rw [← hby]; exact ha'⟩

/-- The rational diagonal of `NonTight.lean` is the existence of a pair of
    strict preferences under which player 1 works in the sense of the summary. -/
theorem rd1_iff_works [Nonempty B] (g : A → B → X) :
    RationalDiagonal1 g ↔ ∃ u v : X → ℕ, Function.Injective u ∧ Function.Injective v ∧
      SummaryAutomaton.Works u (SummaryAutomaton.summary u v g) := by
  constructor
  · rintro ⟨u, v, hu, hv, h⟩
    have hv' := (injective_iff v).mp hv
    exact ⟨u, v, (injective_iff u).mp hu, hv', (works_iff_br hv' g).mpr h⟩
  · rintro ⟨u, v, hu, hv, h⟩
    exact ⟨u, v, (injective_iff u).mpr hu, (injective_iff v).mpr hv, (works_iff_br hv g).mp h⟩

end Summary

end TwoPlayer

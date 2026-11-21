/-
  Theorem 6 of *Walls and Strategy*: let g be a non-dictatorial game
  form with lotteries as outcomes. Then
  (i) some player at some utility scale has no universally correct
      strategist, or
  (ii) g is straightforward, and at some assignment of utility scales no
      profile of dominant strategies yields an ex ante Pareto optimal lottery.

  Proved from Lemma 2 (`Diagonal.diagonal_lemma`) and Corollary 2 of Gibbard (1978),
  "Straightforwardness of game forms with lotteries as outcomes",
  Econometrica 46, 595–614. Corollary 2 is not formalized here; it enters as
  the explicit hypothesis `cor2`.

  Corollary 2 (Gibbard 1978, Section 3): if there are at least three
  alternatives, g is straightforward and g satisfies the ex ante Pareto
  condition, then g is dictatorial.

  The definitions follow Gibbard's Sections 2–3 but are kept abstract:
  outcomes are elements of a type L (in Gibbard: lotteries over a finite set V
  of alternatives), `sure x` is the lottery giving x for certain, utility
  scales form a type U, and `eu u p` is the expected utility of p on scale u,
  with values in a type R carrying ≤ and <. The derivation of Theorem 6 uses
  no property of these: all the arithmetic sits inside Corollary 2. The
  hypothesis `cor2` is Gibbard's theorem exactly when L, U, eu are lotteries,
  utility scales and expected utility over a finite set of at least three
  alternatives, and strategy sets are finite (Gibbard's standing assumption).
  Uses only core Lean.
-/

import Diagonal
import Gibbard73

namespace Lotteries

open Gibbard73

variable {V L U R I St : Type} [DecidableEq I] [LE R] [LT R]

/-- A game form with lotteries as outcomes. -/
structure LotteryGame (V L U R I St : Type) where
  g : (I → St) → L
  sure : V → L
  eu : U → L → R

/-- t is u-dominant for k: U · g(t, v₋ₖ) ≥ U · g(v) for every profile v. -/
def Dominant (G : LotteryGame V L U R I St) (u : U) (k : I) (t : St) : Prop :=
  ∀ s : I → St, G.eu u (G.g s) ≤ G.eu u (G.g (upd s k t))

/-- Every player has a dominant strategy at every utility scale. -/
def Straightforward (G : LotteryGame V L U R I St) : Prop :=
  ∀ (u : U) (k : I), ∃ t : St, Dominant G u k t

/-- k has, for every alternative x, a strategy giving x for certain whatever
    the others do. -/
def IsDictator (G : LotteryGame V L U R I St) (k : I) : Prop :=
  ∀ x : V, ∃ t : St, ∀ s : I → St, s k = t → G.g s = G.sure x

/-- Strategy profile s fits the utility profile us: each sᵢ is usᵢ-dominant. -/
def Fits (G : LotteryGame V L U R I St) (us : I → U) (s : I → St) : Prop :=
  ∀ i, Dominant G (us i) i (s i)

/-- No lottery is better for everyone. -/
def ParetoExAnte (G : LotteryGame V L U R I St) (us : I → U) (p : L) : Prop :=
  ¬ ∃ q : L, ∀ i, G.eu (us i) p < G.eu (us i) q

/-- Gibbard's ex ante Pareto condition: for every utility profile some
    fitting profile of dominant strategies yields an ex ante Pareto optimal
    lottery. -/
def ExAntePareto (G : LotteryGame V L U R I St) : Prop :=
  ∀ us : I → U, ∃ s : I → St, Fits G us s ∧ ParetoExAnte G us (G.g s)

/-- Theorem 6 of *Walls and Strategy*. -/
theorem lottery_dichotomy (G : LotteryGame V L U R I St)
    (cor2 : Straightforward G → ExAntePareto G → ∃ k, IsDictator G k)
    (hnd : ∀ k, ¬ IsDictator G k) :
    (∃ (k : I) (u : U), ∀ (Env : Type) (M : Env → Option St) (opp : Env → Option (I → St)),
        Diagonal.CanSimulate M opp →
        ¬ Diagonal.UniversallyCorrect (fun b r => G.g (upd r k b))
            (fun p q => G.eu u q ≤ G.eu u p) M opp) ∨
    (Straightforward G ∧ ∃ us : I → U, ∀ s, Fits G us s → ¬ ParetoExAnte G us (G.g s)) := by
  by_cases hs : Straightforward G
  · -- (ii): otherwise Corollary 2 would give a dictator
    right
    refine ⟨hs, ?_⟩
    apply Classical.byContradiction
    intro hc
    obtain ⟨k, hk⟩ := cor2 hs (fun us => Classical.byContradiction fun h =>
      hc ⟨us, fun s hf hp => h ⟨s, hf, hp⟩⟩)
    exact hnd k hk
  · -- (i): some player at some scale has no dominant strategy; apply Lemma 2
    left
    obtain ⟨u, k, hk⟩ : ∃ (u : U) (k : I), ∀ t : St, ¬ Dominant G u k t := by
      apply Classical.byContradiction
      intro hc
      apply hs
      intro u k
      apply Classical.byContradiction
      intro ht
      exact hc ⟨u, k, fun t hd => ht ⟨t, hd⟩⟩
    refine ⟨k, u, ?_⟩
    intro Env M opp hsim
    apply Diagonal.diagonal_lemma _ _ M opp _ hsim
    rintro ⟨b, hb⟩
    apply hk b
    intro s
    have h := hb s (s k)
    simp only [upd_self] at h
    exact h

end Lotteries

/-
  Theorem 3 of *Walls and Strategy*: let g be a game form with at least
  three possible outcomes. Either g is dictatorial, or some player at some
  preference ordering has no universally correct strategist.

  Proof: if g is not dictatorial, it is not straightforward (Gibbard 1973,
  `Gibbard73.gibbard`), so some player k at some ordering P has no dominant
  strategy. Lemma 2 (`Diagonal.diagonal_lemma`) then applies to k, with the
  other players' strategies as the opposing profile.
-/

import Diagonal
import Gibbard73

namespace Dichotomy

open Arrow Gibbard73

variable {X I St : Type} [DecidableEq X] [DecidableEq I]

/-- Theorem 3 of *Walls and Strategy*. For a non-dictatorial game form
    there is a player k and an ordering P such that against opponents able to simulate it, no
    strategist for k is universally correct at P. Here player k's ballot b
    against the others' profile r gives the outcome g(r_k/b), and outcome o is
    at least as good as o' when not o' P o. -/
theorem dichotomy (Gf : GameForm X I St) (hnd : ∀ k, ¬ IsDictator Gf.g k) :
    ∃ (k : I) (P : Rel X), IsOrdering P ∧
      ∀ (Env : Type) (M : Env → Option St) (opp : Env → Option (I → St)),
        Diagonal.CanSimulate M opp →
        ¬ Diagonal.UniversallyCorrect (fun b r => Gf.g (upd r k b))
            (fun o o' => P o' o = false) M opp := by
  have hns : ¬ Straightforward Gf.g := fun h => by
    obtain ⟨k, hk⟩ := gibbard Gf h
    exact hnd k hk
  obtain ⟨P, hP, k, hk⟩ :
      ∃ P : Rel X, IsOrdering P ∧ ∃ k : I, ∀ t : St, ¬ Dominant Gf.g P k t := by
    apply Classical.byContradiction
    intro hc
    apply hns
    intro P hP k
    apply Classical.byContradiction
    intro ht
    exact hc ⟨P, hP, k, fun t hd => ht ⟨t, hd⟩⟩
  refine ⟨k, P, hP, ?_⟩
  intro Env M opp hsim
  apply Diagonal.diagonal_lemma _ _ M opp _ hsim
  rintro ⟨b, hb⟩
  apply hk b
  intro s
  have h := hb s (s k)
  simp only [upd_self] at h
  exact h

end Dichotomy

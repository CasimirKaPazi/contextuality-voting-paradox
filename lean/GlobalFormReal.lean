/-
  Section 4 of *The Global Form* (`notes/global-form.md`): the real degree
  and Proposition 2, for three alternatives and any finite set of voters.

  A rule μ gives at each profile a lottery over the six rankings (positions on
  the hexagon of `GlobalForm.lean`). Step k of a voter's loop flips the pair
  `pairOf k`. The rankings pair up along a flip of pair e; `flipDir e y` is +1
  if flipping e moves y forward on the hexagon, −1 if backward, 0 if y has no
  partner. The expected displacement of a step from lottery P to lottery Q is
  `disp e P Q`, half the sum of flipDir e y · (P y − Q y): the note's sum
  over partner pairs, each pair counted from both ends. The real degree
  `rdeg μ i c` is the sum over the six steps of voter i's loop, divided by 6.

  * `rdeg_mix` (Proposition 2, first part): for a mixture of dictatorships and
    anti-dictatorships with weights w j false (dictator j) and w j true
    (anti-dictator j), the real degree of voter i is w i false + w i true, at
    every context. Only the components that follow voter i move along its
    loop, each by one full turn (`flip_two`, finite).
  * `rdeg_dict`, `rdeg_sum`, `rdeg_random`: for a mixture of dictatorships
    with weights λ the real degrees are the weights, do not depend on the
    context and sum to 1; random dictatorship gives every voter 1/n.

  Not formalised here: that the formula is the expected winding of every
  compatible joint draw along the loop, and the second part of Proposition 2
  as stated in the note, which identifies fully compatible unanimous rules
  with mixtures of dictatorships through Theorems 5 and 5′
  (`ArrowBase.theorem5'`). That needs rankings of three candidates, as in
  `ArrowGeneral.lean`, matched with the six positions of the hexagon.
-/

module

public import GlobalForm

@[expose] public section

open Finset GlobalForm

namespace GlobalFormReal

/-! ### Flips on the hexagon -/

/-- The pair flipped by step k of a loop (ab, ac, bc, ab, ac, bc). -/
def pairOf (k : Fin 6) : Fin 3 := ⟨k.val % 3, Nat.mod_lt _ (by decide)⟩

/-- +1 if flipping pair e moves y forward, −1 if backward, 0 if no partner. -/
def flipDir (e : Fin 3) (y : Fin 6) : ℤ :=
  if e = pairOf y then 1 else if e = pairOf (y - 1) then -1 else 0

/-- A forward step of a dictator, and of an anti-dictator half a turn away,
    moves by one edge in the direction of the step. -/
lemma flip_two : ∀ k : Fin 6,
    flipDir (pairOf k) k - flipDir (pairOf k) (k + 1) = 2 ∧
      flipDir (pairOf k) (k + 3) - flipDir (pairOf k) (k + 1 + 3) = 2 := by
  decide

/-- The point mass at x. -/
def ind (x y : Fin 6) : ℝ := if y = x then 1 else 0

/-- The expected displacement of a step flipping e, from lottery P to Q. -/
noncomputable def disp (e : Fin 3) (P Q : Fin 6 → ℝ) : ℝ :=
  (1 / 2) * ∑ y, (flipDir e y : ℝ) * (P y - Q y)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real degree of voter i at context c. -/
noncomputable def rdeg (μ : (ι → Fin 6) → Fin 6 → ℝ) (i : ι) (c : ι → Fin 6) : ℝ :=
  (1 / 6) * ∑ k : Fin 6, disp (pairOf k) (μ (setS {i} k c)) (μ (setS {i} (k + 1) c))

/-! ### Mixtures of dictatorships and anti-dictatorships -/

/-- The ranking of component (j, s): voter j's ranking, reversed when s. -/
def comp (π : ι → Fin 6) (j : ι) (s : Bool) : Fin 6 := if s then π j + 3 else π j

/-- The mixture with weight w j false on j's dictatorship and w j true on j's
    anti-dictatorship. -/
noncomputable def mixDA (w : ι → Bool → ℝ) (π : ι → Fin 6) (y : Fin 6) : ℝ :=
  ∑ j, ∑ s : Bool, w j s * ind (comp π j s) y

omit [DecidableEq ι] in
lemma lin_mix (f : Fin 6 → ℝ) (c : ι → Bool → ℝ) (x : ι → Bool → Fin 6) :
    ∑ y, f y * (∑ j, ∑ s : Bool, c j s * ind (x j s) y) = ∑ j, ∑ s : Bool, c j s * f (x j s) := by
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [Fintype.sum_eq_single (x j s) (fun y hy => by simp [ind, hy])]
  simp only [ind, ↓reduceIte]
  ring

omit [DecidableEq ι] in
lemma disp_mix (w : ι → Bool → ℝ) (e : Fin 3) (πa πb : ι → Fin 6) :
    disp e (mixDA w πa) (mixDA w πb) =
      (1 / 2) * ∑ j, ∑ s : Bool,
        w j s * ((flipDir e (comp πa j s) : ℝ) - flipDir e (comp πb j s)) := by
  unfold disp mixDA
  congr 1
  calc ∑ y, (flipDir e y : ℝ) * ((∑ j, ∑ s : Bool, w j s * ind (comp πa j s) y) -
        ∑ j, ∑ s : Bool, w j s * ind (comp πb j s) y)
      = ∑ y, (flipDir e y : ℝ) * (∑ j, ∑ s : Bool, w j s * ind (comp πa j s) y) -
        ∑ y, (flipDir e y : ℝ) * (∑ j, ∑ s : Bool, w j s * ind (comp πb j s) y) := by
        rw [← sum_sub_distrib]
        exact sum_congr rfl fun y _ => mul_sub _ _ _
    _ = ∑ j, ∑ s : Bool, w j s * (flipDir e (comp πa j s) : ℝ) -
        ∑ j, ∑ s : Bool, w j s * (flipDir e (comp πb j s) : ℝ) := by
        rw [lin_mix, lin_mix]
    _ = ∑ j, ∑ s : Bool, w j s * ((flipDir e (comp πa j s) : ℝ) - flipDir e (comp πb j s)) := by
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun j _ => ?_
        rw [← sum_sub_distrib]
        exact sum_congr rfl fun s _ => (mul_sub _ _ _).symm

/-- **Proposition 2, first part.** For a mixture of dictatorships and
    anti-dictatorships, the real degree of voter i is the total weight of i's
    dictatorship and anti-dictatorship, at every context. -/
theorem rdeg_mix (w : ι → Bool → ℝ) (i : ι) (c : ι → Fin 6) :
    rdeg (mixDA w) i c = w i false + w i true := by
  unfold rdeg
  have step : ∀ k : Fin 6, disp (pairOf k) (mixDA w (setS {i} k c))
      (mixDA w (setS {i} (k + 1) c)) = w i false + w i true := by
    intro k
    rw [disp_mix]
    rw [Fintype.sum_eq_single i]
    · rw [Fintype.sum_bool]
      have e1 : comp (setS {i} k c) i true = k + 3 := by unfold comp setS; simp
      have e2 : comp (setS {i} (k + 1) c) i true = k + 1 + 3 := by unfold comp setS; simp
      have e3 : comp (setS {i} k c) i false = k := by unfold comp setS; simp
      have e4 : comp (setS {i} (k + 1) c) i false = k + 1 := by unfold comp setS; simp
      have h1 : ((flipDir (pairOf k) k : ℤ) : ℝ) - (flipDir (pairOf k) (k + 1) : ℝ) = 2 := by
        exact_mod_cast (flip_two k).1
      have h2 : ((flipDir (pairOf k) (k + 3) : ℤ) : ℝ) - (flipDir (pairOf k) (k + 1 + 3) : ℝ) =
          2 := by
        exact_mod_cast (flip_two k).2
      rw [e1, e2, e3, e4, h1, h2]
      ring
    · intro j hj
      have hc : ∀ s, comp (setS {i} k c) j s = comp (setS {i} (k + 1) c) j s := fun s => by
        unfold comp setS
        simp [hj]
      simp [hc]
  rw [sum_congr rfl fun k _ => step k]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- A mixture of dictatorships alone. -/
def dictW (lam : ι → ℝ) (j : ι) (s : Bool) : ℝ := if s then 0 else lam j

/-- **Proposition 2, for mixtures of dictatorships.** The real degrees are the
    weights, at every context. -/
theorem rdeg_dict (lam : ι → ℝ) (i : ι) (c : ι → Fin 6) :
    rdeg (mixDA (dictW lam)) i c = lam i := by
  rw [rdeg_mix]
  simp [dictW]

/-- The real degrees of a mixture of dictatorships with total weight 1 sum to 1. -/
theorem rdeg_sum (lam : ι → ℝ) (h1 : ∑ j, lam j = 1) (c : ι → Fin 6) :
    ∑ i, rdeg (mixDA (dictW lam)) i c = 1 := by
  simp only [rdeg_dict]
  exact h1

/-- Random dictatorship gives every voter real degree 1/n. -/
theorem rdeg_random (i : ι) (c : ι → Fin 6) :
    rdeg (mixDA (dictW fun _ => 1 / (Fintype.card ι : ℝ))) i c = 1 / Fintype.card ι :=
  rdeg_dict _ i c

end GlobalFormReal

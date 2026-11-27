/-
  Proposition 4 of *The Global Form* (`notes/global-form.md`, Section 7): for
  one voter and three alternatives, the SD-SP lotteries are exactly the
  mixtures of the seven deterministic SP rules and the random top two; the
  degree is at least −1/2; in every mixture the random top two has weight at
  least −2 times the degree, and this bound is attained.

  Encoding. The six rankings of a, b, c (outcomes 0, 1, 2) in the order of
  the hexagon: abc, acb, cab, cba, bca, bac, with their top and second
  (`top`, `sec`). A rule is a function `f : Fin 6 → Fin 3 → ℝ`, a lottery at
  each ranking (`Lottery`). Strategy-proofness in the sense of stochastic
  dominance (`SDSP`): reporting any ranking r' instead of the true r gives at
  most as much probability to the top of r, and to the top two of r.

  The eight rules (`mix`, weights in this order): the constants a, b, c; the
  better of a and b, of b and c, of a and c (`bab`, `bbc`, `bac`); the
  dictatorship (`top`); the random top two, top or second with probability
  1/2 each.

  The degree (`deg`) is the expected winding: a third of the sum, over the six
  steps of the hexagon, of the probability moved forward minus the
  probability moved backward. Each step swaps one pair; the probability moved
  is what the alternative that drops loses.

  * `decomp`: an SD-SP lottery rule is a mixture of the eight, with the random
    top two weighted max(0, −2 · degree). The weights are the note's: with
    D = deg ≥ 0 the dictatorship gets D, each "better of two" the backward
    flow along its edge, the constants the rest; with D < 0 the random top
    two gets −2D and the backward flows are reduced by −D.
  * `mix_sdsp`, `lottery_mix`, `prop4`: conversely every mixture is an SD-SP
    lottery rule, so the SD-SP lotteries are exactly the mixtures.
  * `deg_mix`, `deg_ge`, `topTwo_weight`: the degree of a mixture is the
    weight of the dictatorship minus half that of the random top two; hence
    the degree is at least −1/2, and the random top two has weight at least
    −2 · degree in every mixture.

  The equalities and inequalities are linear consequences of the SD-SP and
  lottery conditions, instantiated at all pairs of rankings and closed by
  `linarith`. Not here: Proposition 5 (any number of voters), which rests on
  Gibbard's 1977 theorem.
-/

module

public import Mathlib

@[expose] public section

namespace GlobalFormLottery

/-- A one-voter lottery rule on the six rankings of three alternatives. -/
abbrev Rule := Fin 6 → Fin 3 → ℝ

/-- The top of each ranking: abc, acb, cab, cba, bca, bac. -/
def top : Fin 6 → Fin 3 := ![0, 0, 2, 2, 1, 1]
/-- The second of each ranking. -/
def sec : Fin 6 → Fin 3 := ![1, 2, 0, 1, 2, 0]
/-- The better of a and b at each ranking. -/
def bab : Fin 6 → Fin 3 := ![0, 0, 0, 1, 1, 1]
/-- The better of b and c at each ranking. -/
def bbc : Fin 6 → Fin 3 := ![1, 2, 2, 2, 1, 1]
/-- The better of a and c at each ranking. -/
def bac : Fin 6 → Fin 3 := ![0, 0, 2, 2, 2, 0]

/-- The point mass at x. -/
noncomputable def pt (x y : Fin 3) : ℝ := if y = x then 1 else 0

/-- A lottery at every ranking. -/
def Lottery (f : Rule) : Prop := ∀ r, (∀ x, 0 ≤ f r x) ∧ f r 0 + f r 1 + f r 2 = 1

/-- Strategy-proofness in the sense of stochastic dominance, for one voter. -/
def SDSP (f : Rule) : Prop :=
  ∀ r r' : Fin 6, f r' (top r) ≤ f r (top r) ∧
    f r' (top r) + f r' (sec r) ≤ f r (top r) + f r (sec r)

/-- The mixture of the eight rules: constants a, b, c; the better of a and b,
    of b and c, of a and c; the dictatorship; the random top two. -/
noncomputable def mix (w : Fin 8 → ℝ) : Rule := fun r x =>
  w 0 * pt 0 x + w 1 * pt 1 x + w 2 * pt 2 x + w 3 * pt (bab r) x + w 4 * pt (bbc r) x +
    w 5 * pt (bac r) x + w 6 * pt (top r) x + w 7 * ((pt (top r) x + pt (sec r) x) / 2)

/-- The degree: the expected winding along the hexagon. The six flows are what
    the dropping alternative loses at each step: b at abc → acb, a at
    acb → cab, a at cab → cba, c at cba → bca, c at bca → bac, b at bac → abc;
    the even steps move the voter's top, the odd steps do not. -/
noncomputable def deg (f : Rule) : ℝ :=
  (-(f 0 1 - f 1 1) + (f 1 0 - f 2 0) - (f 2 0 - f 3 0) + (f 3 2 - f 4 2) - (f 4 2 - f 5 2) +
    (f 5 1 - f 0 1)) / 3

/-! ### Mixtures are SD-SP lotteries -/

theorem mix_sdsp {w : Fin 8 → ℝ} (hw : ∀ j, 0 ≤ w j) : SDSP (mix w) := by
  have h0 := hw 0; have h1 := hw 1; have h2 := hw 2; have h3 := hw 3
  have h4 := hw 4; have h5 := hw 5; have h6 := hw 6; have h7 := hw 7
  intro r r'
  fin_cases r <;> fin_cases r' <;> refine ⟨?_, ?_⟩ <;>
    simp [mix, pt, top, sec, bab, bbc, bac] <;> linarith

theorem lottery_mix {w : Fin 8 → ℝ} (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j = 1) :
    Lottery (mix w) := by
  have h0 := hw 0; have h1 := hw 1; have h2 := hw 2; have h3 := hw 3
  have h4 := hw 4; have h5 := hw 5; have h6 := hw 6; have h7 := hw 7
  rw [Fin.sum_univ_eight] at hs
  intro r
  refine ⟨fun x => ?_, ?_⟩
  · fin_cases r <;> fin_cases x <;> simp [mix, pt, top, sec, bab, bbc, bac] <;> linarith
  · fin_cases r <;> simp [mix, pt, top, sec, bab, bbc, bac] <;> linarith

/-! ### The degree of a mixture -/

theorem deg_mix (w : Fin 8 → ℝ) : deg (mix w) = w 6 - w 7 / 2 := by
  simp [deg, mix, pt, top, sec, bab, bbc, bac]
  ring

lemma slack {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a = 0 ∨ b = 0) :
    b = max 0 (-2 * (a - b / 2)) := by
  rcases h with rfl | rfl
  · rw [max_eq_right (by linarith)]
    ring
  · rw [max_eq_left (by linarith)]

/-! ### SD-SP lotteries are mixtures -/

/-- **Decomposition.** An SD-SP lottery rule is a mixture of the eight rules,
    with the random top two weighted max(0, −2 · degree). -/
theorem decomp {f : Rule} (hL : Lottery f) (hS : SDSP f) :
    ∃ w : Fin 8 → ℝ, (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ f = mix w ∧
      w 7 = max 0 (-2 * deg f) := by
  obtain ⟨hn0, hs0⟩ := hL 0
  have l00 := hn0 0
  have l01 := hn0 1
  have l02 := hn0 2
  obtain ⟨hn1, hs1⟩ := hL 1
  have l10 := hn1 0
  have l11 := hn1 1
  have l12 := hn1 2
  obtain ⟨hn2, hs2⟩ := hL 2
  have l20 := hn2 0
  have l21 := hn2 1
  have l22 := hn2 2
  obtain ⟨hn3, hs3⟩ := hL 3
  have l30 := hn3 0
  have l31 := hn3 1
  have l32 := hn3 2
  obtain ⟨hn4, hs4⟩ := hL 4
  have l40 := hn4 0
  have l41 := hn4 1
  have l42 := hn4 2
  obtain ⟨hn5, hs5⟩ := hL 5
  have l50 := hn5 0
  have l51 := hn5 1
  have l52 := hn5 2
  obtain ⟨p01, q01⟩ : f 1 0 ≤ f 0 0 ∧ f 1 0 + f 1 1 ≤ f 0 0 + f 0 1 := hS 0 1
  obtain ⟨p02, q02⟩ : f 2 0 ≤ f 0 0 ∧ f 2 0 + f 2 1 ≤ f 0 0 + f 0 1 := hS 0 2
  obtain ⟨p03, q03⟩ : f 3 0 ≤ f 0 0 ∧ f 3 0 + f 3 1 ≤ f 0 0 + f 0 1 := hS 0 3
  obtain ⟨p04, q04⟩ : f 4 0 ≤ f 0 0 ∧ f 4 0 + f 4 1 ≤ f 0 0 + f 0 1 := hS 0 4
  obtain ⟨p05, q05⟩ : f 5 0 ≤ f 0 0 ∧ f 5 0 + f 5 1 ≤ f 0 0 + f 0 1 := hS 0 5
  obtain ⟨p10, q10⟩ : f 0 0 ≤ f 1 0 ∧ f 0 0 + f 0 2 ≤ f 1 0 + f 1 2 := hS 1 0
  obtain ⟨p12, q12⟩ : f 2 0 ≤ f 1 0 ∧ f 2 0 + f 2 2 ≤ f 1 0 + f 1 2 := hS 1 2
  obtain ⟨p13, q13⟩ : f 3 0 ≤ f 1 0 ∧ f 3 0 + f 3 2 ≤ f 1 0 + f 1 2 := hS 1 3
  obtain ⟨p14, q14⟩ : f 4 0 ≤ f 1 0 ∧ f 4 0 + f 4 2 ≤ f 1 0 + f 1 2 := hS 1 4
  obtain ⟨p15, q15⟩ : f 5 0 ≤ f 1 0 ∧ f 5 0 + f 5 2 ≤ f 1 0 + f 1 2 := hS 1 5
  obtain ⟨p20, q20⟩ : f 0 2 ≤ f 2 2 ∧ f 0 2 + f 0 0 ≤ f 2 2 + f 2 0 := hS 2 0
  obtain ⟨p21, q21⟩ : f 1 2 ≤ f 2 2 ∧ f 1 2 + f 1 0 ≤ f 2 2 + f 2 0 := hS 2 1
  obtain ⟨p23, q23⟩ : f 3 2 ≤ f 2 2 ∧ f 3 2 + f 3 0 ≤ f 2 2 + f 2 0 := hS 2 3
  obtain ⟨p24, q24⟩ : f 4 2 ≤ f 2 2 ∧ f 4 2 + f 4 0 ≤ f 2 2 + f 2 0 := hS 2 4
  obtain ⟨p25, q25⟩ : f 5 2 ≤ f 2 2 ∧ f 5 2 + f 5 0 ≤ f 2 2 + f 2 0 := hS 2 5
  obtain ⟨p30, q30⟩ : f 0 2 ≤ f 3 2 ∧ f 0 2 + f 0 1 ≤ f 3 2 + f 3 1 := hS 3 0
  obtain ⟨p31, q31⟩ : f 1 2 ≤ f 3 2 ∧ f 1 2 + f 1 1 ≤ f 3 2 + f 3 1 := hS 3 1
  obtain ⟨p32, q32⟩ : f 2 2 ≤ f 3 2 ∧ f 2 2 + f 2 1 ≤ f 3 2 + f 3 1 := hS 3 2
  obtain ⟨p34, q34⟩ : f 4 2 ≤ f 3 2 ∧ f 4 2 + f 4 1 ≤ f 3 2 + f 3 1 := hS 3 4
  obtain ⟨p35, q35⟩ : f 5 2 ≤ f 3 2 ∧ f 5 2 + f 5 1 ≤ f 3 2 + f 3 1 := hS 3 5
  obtain ⟨p40, q40⟩ : f 0 1 ≤ f 4 1 ∧ f 0 1 + f 0 2 ≤ f 4 1 + f 4 2 := hS 4 0
  obtain ⟨p41, q41⟩ : f 1 1 ≤ f 4 1 ∧ f 1 1 + f 1 2 ≤ f 4 1 + f 4 2 := hS 4 1
  obtain ⟨p42, q42⟩ : f 2 1 ≤ f 4 1 ∧ f 2 1 + f 2 2 ≤ f 4 1 + f 4 2 := hS 4 2
  obtain ⟨p43, q43⟩ : f 3 1 ≤ f 4 1 ∧ f 3 1 + f 3 2 ≤ f 4 1 + f 4 2 := hS 4 3
  obtain ⟨p45, q45⟩ : f 5 1 ≤ f 4 1 ∧ f 5 1 + f 5 2 ≤ f 4 1 + f 4 2 := hS 4 5
  obtain ⟨p50, q50⟩ : f 0 1 ≤ f 5 1 ∧ f 0 1 + f 0 0 ≤ f 5 1 + f 5 0 := hS 5 0
  obtain ⟨p51, q51⟩ : f 1 1 ≤ f 5 1 ∧ f 1 1 + f 1 0 ≤ f 5 1 + f 5 0 := hS 5 1
  obtain ⟨p52, q52⟩ : f 2 1 ≤ f 5 1 ∧ f 2 1 + f 2 0 ≤ f 5 1 + f 5 0 := hS 5 2
  obtain ⟨p53, q53⟩ : f 3 1 ≤ f 5 1 ∧ f 3 1 + f 3 0 ≤ f 5 1 + f 5 0 := hS 5 3
  obtain ⟨p54, q54⟩ : f 4 1 ≤ f 5 1 ∧ f 4 1 + f 4 0 ≤ f 5 1 + f 5 0 := hS 5 4
  by_cases hD : 0 ≤ (f 1 0 - f 2 0 - (f 4 2 - f 5 2))
  · let W : Fin 8 → ℝ := ![f 0 0 - (f 1 0 - f 2 0 - (f 4 2 - f 5 2)) - (f 2 0 - f 3 0) - (f 4 2 - f 5 2), f 1 1, f 0 2, (f 2 0 - f 3 0), (f 0 1 - f 1 1), (f 4 2 - f 5 2), (f 1 0 - f 2 0 - (f 4 2 - f 5 2)), 0]
    have hW : ∀ j, 0 ≤ W j := by
      intro j
      fin_cases j <;> simp [W] <;> linarith
    have hf : f = mix W := by
      funext r x
      fin_cases r <;> fin_cases x <;> simp [W, mix, pt, top, sec, bab, bbc, bac] <;> linarith
    refine ⟨W, hW, ?_, hf, ?_⟩
    · simp [W, Fin.sum_univ_eight]
      linarith
    · rw [hf, deg_mix]
      exact slack (hW 6) (hW 7) (Or.inr (by simp [W]))
  · let W : Fin 8 → ℝ := ![f 0 0 - (f 2 0 - f 3 0) - (f 4 2 - f 5 2) - (f 1 0 - f 2 0 - (f 4 2 - f 5 2)), f 1 1, f 0 2, (f 2 0 - f 3 0) + (f 1 0 - f 2 0 - (f 4 2 - f 5 2)), (f 0 1 - f 1 1) + (f 1 0 - f 2 0 - (f 4 2 - f 5 2)), (f 4 2 - f 5 2) + (f 1 0 - f 2 0 - (f 4 2 - f 5 2)), 0, -2 * (f 1 0 - f 2 0 - (f 4 2 - f 5 2))]
    have hW : ∀ j, 0 ≤ W j := by
      intro j
      fin_cases j <;> simp [W] <;> linarith
    have hf : f = mix W := by
      funext r x
      fin_cases r <;> fin_cases x <;> simp [W, mix, pt, top, sec, bab, bbc, bac] <;> linarith
    refine ⟨W, hW, ?_, hf, ?_⟩
    · simp [W, Fin.sum_univ_eight]
      linarith
    · rw [hf, deg_mix]
      exact slack (hW 6) (hW 7) (Or.inl (by simp [W]))

/-- **Proposition 4, first part.** The SD-SP lotteries for one voter and three
    alternatives are exactly the mixtures of the eight rules. -/
theorem prop4 (f : Rule) :
    (Lottery f ∧ SDSP f) ↔ ∃ w : Fin 8 → ℝ, (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ f = mix w := by
  constructor
  · rintro ⟨hL, hS⟩
    obtain ⟨w, hw, hs, hf, -⟩ := decomp hL hS
    exact ⟨w, hw, hs, hf⟩
  · rintro ⟨w, hw, hs, rfl⟩
    exact ⟨lottery_mix hw hs, mix_sdsp hw⟩

/-- **Proposition 4, the degree.** In every mixture the random top two has
    weight at least −2 · degree. -/
theorem topTwo_weight {f : Rule} {w : Fin 8 → ℝ} (hw : ∀ j, 0 ≤ w j) (hf : f = mix w) :
    -2 * deg f ≤ w 7 := by
  rw [hf, deg_mix]
  linarith [hw 6]

/-- **Proposition 4, the bound.** The degree of an SD-SP lottery rule is at
    least −1/2. -/
theorem deg_ge {f : Rule} (hL : Lottery f) (hS : SDSP f) : -1 / 2 ≤ deg f := by
  obtain ⟨w, hw, hs, hf, -⟩ := decomp hL hS
  rw [Fin.sum_univ_eight] at hs
  rw [hf, deg_mix]
  linarith [hw 0, hw 1, hw 2, hw 3, hw 4, hw 5, hw 6]

end GlobalFormLottery

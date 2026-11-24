/-
  Arrow's theorem in the form used by Gibbard (1973, Section 3), as the first
  step towards Gibbard's theorem on straightforward game forms.
  Uses only core Lean, no Mathlib.

  Gibbard's definitions:
  * An ordering of X is a relation P ("is preferred to") with
      (1a) not (x P y and y P x),
      (1b) x P z implies x P y or y P z.
    Ties (indifference) are allowed.
  * A social welfare function f assigns an ordering to every n-tuple of
    orderings.
  * Arrow conditions: Scope (at least three outcomes), Unanimity, Pairwise
    Determination, Non-dictatorship; a dictator for f is a k such that
    x P_k y implies x f(P) y for all P, x, y.

  Here the outcomes form a type X with a list containing all of them, and the
  voters a type I with a list containing all of them (so both are finite).

  Proof: decisive coalitions. A coalition G is (weakly) decisive for (x, y)
  if f puts x above y whenever G puts x above y and everyone else y above x.
  (1) Decisive for one pair implies decisive for every pair.
  (2) Everyone together is decisive (Unanimity).
  (3) If G is decisive and is split into two parts, one part is decisive.
  (4) Splitting off one voter at a time leaves a single decisive voter.
  (5) A decisive single voter is a dictator.
  The profiles needed along the way are built from rank functions: any
  function X → ℕ defines an ordering, and every ordering comes from one
  (rank = number of alternatives strictly above).
-/

module

@[expose] public section

namespace Arrow

variable {X I : Type}

abbrev Rel (X : Type) := X → X → Bool

/-- Gibbard's orderings: asymmetric (1a) and negatively transitive (1b). -/
structure IsOrdering (P : Rel X) : Prop where
  asymm : ∀ x y, P x y = true → P y x = false
  negTrans : ∀ x y z, P x z = true → P x y = true ∨ P y z = true

theorem ord_trans {P : Rel X} (hP : IsOrdering P) {x y z : X}
    (h₁ : P x y = true) (h₂ : P y z = true) : P x z = true := by
  rcases hP.negTrans x z y h₁ with h | h
  · exact h
  · have h' := hP.asymm y z h₂
    rw [h] at h'
    cases h'

theorem ord_irrefl {P : Rel X} (hP : IsOrdering P) (x : X) : P x x = false := by
  cases h : P x x with
  | false => rfl
  | true =>
    have h' := hP.asymm x x h
    rw [h] at h'
    cases h'

/-- Arrow's conditions other than Scope and Non-dictatorship, for a social
    welfare function on profiles indexed by I. -/
structure ArrowConditions (f : (I → Rel X) → Rel X) : Prop where
  ordering : ∀ P : I → Rel X, (∀ i, IsOrdering (P i)) → IsOrdering (f P)
  unanimity : ∀ P : I → Rel X, (∀ i, IsOrdering (P i)) →
    ∀ x y, (∀ i, P i x y = true) → f P x y = true
  pairwise : ∀ P P' : I → Rel X, (∀ i, IsOrdering (P i)) → (∀ i, IsOrdering (P' i)) →
    ∀ x y, (∀ i, P i x y = P' i x y) → (∀ i, P i y x = P' i y x) → f P x y = f P' x y

/-! ### Counting and ranks -/

def countIf {V : Type} (P : V → Bool) : List V → Nat
  | [] => 0
  | i :: vs =>
    match P i with
    | true => countIf P vs + 1
    | false => countIf P vs

theorem countIf_mono {V : Type} (A B : V → Bool) (h : ∀ t, A t = true → B t = true) :
    ∀ l : List V, countIf A l ≤ countIf B l
  | [] => Nat.le_refl 0
  | i :: l => by
    have ih := countIf_mono A B h l
    cases ha : A i with
    | true =>
      have hb : B i = true := h i ha
      simp only [countIf, ha, hb]
      omega
    | false =>
      cases hb : B i <;> simp only [countIf, ha, hb] <;> omega

theorem countIf_strict {V : Type} (A B : V → Bool) (h : ∀ t, A t = true → B t = true)
    (t : V) (hBt : B t = true) (hAt : A t = false) :
    ∀ l : List V, t ∈ l → countIf A l < countIf B l
  | [], hl => by cases hl
  | u :: l, hl => by
    have hm := countIf_mono A B h l
    rcases List.mem_cons.mp hl with e | e
    · have hBu : B u = true := e ▸ hBt
      have hAu : A u = false := e ▸ hAt
      simp only [countIf, hAu, hBu]
      omega
    · have ih := countIf_strict A B h t hBt hAt l e
      cases ha : A u with
      | true =>
        have hb : B u = true := h u ha
        simp only [countIf, ha, hb]
        omega
      | false =>
        cases hb : B u <;> simp only [countIf, ha, hb] <;> omega

/-- Number of alternatives strictly above x. -/
def above (allX : List X) (P : Rel X) (x : X) : Nat :=
  countIf (fun t => P t x) allX

/-- Every ordering is represented by its rank function. -/
theorem rank_spec (allX : List X) (hallX : ∀ x, x ∈ allX) (P : Rel X) (hP : IsOrdering P)
    (x y : X) : P x y = true ↔ above allX P x < above allX P y := by
  constructor
  · intro h
    exact countIf_strict (fun t => P t x) (fun t => P t y)
      (fun t ht => ord_trans hP ht h) x h (ord_irrefl hP x) allX (hallX x)
  · intro hlt
    cases hxy : P x y with
    | true => rfl
    | false =>
      have hle : above allX P y ≤ above allX P x :=
        countIf_mono (fun t => P t y) (fun t => P t x) (fun t ht => by
          rcases hP.negTrans t x y ht with h | h
          · exact h
          · rw [hxy] at h
            cases h) allX
      omega

/-- The ordering defined by a rank function (smaller rank is better). -/
def relOf (r : X → Nat) : Rel X := fun s t => decide (r s < r t)

theorem relOf_iff (r : X → Nat) (s t : X) : relOf r s t = true ↔ r s < r t := by
  simp [relOf]

theorem relOf_ord (r : X → Nat) : IsOrdering (relOf r) where
  asymm := by
    intro x y h
    rw [relOf_iff] at h
    simp only [relOf, decide_eq_false_iff_not]
    omega
  negTrans := by
    intro x y z h
    rw [relOf_iff] at h
    rw [relOf_iff, relOf_iff]
    omega

/-- A rank function that is 3·r + 3 at t and u gives the same comparison of
    t and u as r. -/
theorem agree (r r' : X → Nat) (P : Rel X) (hP : ∀ s t, P s t = true ↔ r s < r t)
    (t u : X) (ht : r' t = 3 * r t + 3) (hu : r' u = 3 * r u + 3) :
    relOf r' t u = P t u := by
  cases hp : P t u with
  | true =>
    have h := (hP t u).mp hp
    rw [relOf_iff]
    omega
  | false =>
    have h : ¬ r t < r u := fun hc => by
      rw [(hP t u).mpr hc] at hp
      cases hp
    simp only [relOf, decide_eq_false_iff_not]
    omega

/-! ### The setting -/

/-- Outcomes, a social welfare function satisfying the Arrow conditions, and
    three distinct outcomes (Scope). -/
structure Setting (X I : Type) where
  allX : List X
  hallX : ∀ x, x ∈ allX
  f : (I → Rel X) → Rel X
  hf : ArrowConditions f
  a : X
  b : X
  c : X
  hab : a ≠ b
  hac : a ≠ c
  hbc : b ≠ c

variable [DecidableEq X] [DecidableEq I]

/-- G is decisive for (x, y): if G puts x above y and everyone else y above
    x, then f puts x above y. -/
def W (S : Setting X I) (G : I → Bool) (x y : X) : Prop :=
  ∀ P : I → Rel X, (∀ i, IsOrdering (P i)) → (∀ i, G i = true → P i x y = true) →
    (∀ i, G i = false → P i y x = true) → S.f P x y = true

/-- Insert b just above c. -/
def insertAbove (r : X → Nat) (b c : X) : X → Nat :=
  fun t => if t = b then 3 * r c + 2 else 3 * r t + 3

/-- Insert b just below c. -/
def insertBelow (r : X → Nat) (b c : X) : X → Nat :=
  fun t => if t = b then 3 * r c + 4 else 3 * r t + 3

/-- Put b on top. -/
def putTop (r : X → Nat) (b : X) : X → Nat :=
  fun t => if t = b then 0 else 3 * r t + 3

theorem insA_b (r : X → Nat) (b c : X) : insertAbove r b c b = 3 * r c + 2 := by
  simp [insertAbove]
theorem insA_t (r : X → Nat) (b c t : X) (h : t ≠ b) : insertAbove r b c t = 3 * r t + 3 := by
  simp [insertAbove, h]
theorem insB_b (r : X → Nat) (b c : X) : insertBelow r b c b = 3 * r c + 4 := by
  simp [insertBelow]
theorem insB_t (r : X → Nat) (b c t : X) (h : t ≠ b) : insertBelow r b c t = 3 * r t + 3 := by
  simp [insertBelow, h]
theorem top_b (r : X → Nat) (b : X) : putTop r b b = 0 := by
  simp [putTop]
theorem top_t (r : X → Nat) (b t : X) (h : t ≠ b) : putTop r b t = 3 * r t + 3 := by
  simp [putTop, h]

omit [DecidableEq I] in
/-- For any two outcomes there is a third. -/
theorem third (S : Setting X I) (x y : X) : ∃ w, w ≠ x ∧ w ≠ y := by
  by_cases h : S.a ≠ x ∧ S.a ≠ y
  · exact ⟨S.a, h⟩
  · by_cases h' : S.b ≠ x ∧ S.b ≠ y
    · exact ⟨S.b, h'⟩
    · refine ⟨S.c, fun hcx => ?_, fun hcy => ?_⟩
      · have hax : S.a ≠ x := fun e => S.hac (e.trans hcx.symm)
        have hbx : S.b ≠ x := fun e => S.hbc (e.trans hcx.symm)
        have hay : S.a = y := Classical.byContradiction fun n => h ⟨hax, n⟩
        have hby : S.b = y := Classical.byContradiction fun n => h' ⟨hbx, n⟩
        exact S.hab (hay.trans hby.symm)
      · have hay : S.a ≠ y := fun e => S.hac (e.trans hcy.symm)
        have hby : S.b ≠ y := fun e => S.hbc (e.trans hcy.symm)
        have hax : S.a = x := Classical.byContradiction fun n => h ⟨n, hay⟩
        have hbx : S.b = x := Classical.byContradiction fun n => h' ⟨n, hby⟩
        exact S.hab (hax.trans hbx.symm)

/-! ### (1) Field expansion -/

omit [DecidableEq I] in
/-- Decisive for (a, b) implies decisive for (a, c). -/
theorem expandRight (S : Setting X I) (G : I → Bool) (a b c : X)
    (hW : W S G a b) (hab : a ≠ b) (hcb : c ≠ b) : W S G a c := by
  intro P hP hG hO
  obtain ⟨r, hr⟩ : ∃ r : I → X → Nat, ∀ i s t, P i s t = true ↔ r i s < r i t :=
    ⟨fun i => above S.allX (P i), fun i s t => rank_spec S.allX S.hallX (P i) (hP i) s t⟩
  let P' : I → Rel X := fun i => relOf (insertAbove (r i) b c)
  have hP' : ∀ i, IsOrdering (P' i) := fun i => relOf_ord _
  have h₁ : S.f P' a b = true := by
    apply hW P' hP'
    · intro i hi
      have h := (hr i a c).mp (hG i hi)
      show relOf (insertAbove (r i) b c) a b = true
      rw [relOf_iff, insA_t (r i) b c a hab, insA_b]
      omega
    · intro i hi
      have h := (hr i c a).mp (hO i hi)
      show relOf (insertAbove (r i) b c) b a = true
      rw [relOf_iff, insA_b, insA_t (r i) b c a hab]
      omega
  have h₂ : S.f P' b c = true := by
    apply S.hf.unanimity P' hP'
    intro i
    show relOf (insertAbove (r i) b c) b c = true
    rw [relOf_iff, insA_b, insA_t (r i) b c c hcb]
    omega
  have h₃ : S.f P' a c = true := ord_trans (S.hf.ordering P' hP') h₁ h₂
  have e : S.f P a c = S.f P' a c :=
    S.hf.pairwise P P' hP hP' a c
      (fun i => (agree (r i) _ (P i) (hr i) a c
        (insA_t (r i) b c a hab) (insA_t (r i) b c c hcb)).symm)
      (fun i => (agree (r i) _ (P i) (hr i) c a
        (insA_t (r i) b c c hcb) (insA_t (r i) b c a hab)).symm)
  rw [e]
  exact h₃

omit [DecidableEq I] in
/-- Decisive for (a, b) implies decisive for (c, b). -/
theorem expandLeft (S : Setting X I) (G : I → Bool) (a b c : X)
    (hW : W S G a b) (hac : a ≠ c) (hab : a ≠ b) : W S G c b := by
  intro P hP hG hO
  obtain ⟨r, hr⟩ : ∃ r : I → X → Nat, ∀ i s t, P i s t = true ↔ r i s < r i t :=
    ⟨fun i => above S.allX (P i), fun i s t => rank_spec S.allX S.hallX (P i) (hP i) s t⟩
  let P' : I → Rel X := fun i => relOf (insertBelow (r i) a c)
  have hP' : ∀ i, IsOrdering (P' i) := fun i => relOf_ord _
  have h₁ : S.f P' a b = true := by
    apply hW P' hP'
    · intro i hi
      have h := (hr i c b).mp (hG i hi)
      show relOf (insertBelow (r i) a c) a b = true
      rw [relOf_iff, insB_b, insB_t (r i) a c b (Ne.symm hab)]
      omega
    · intro i hi
      have h := (hr i b c).mp (hO i hi)
      show relOf (insertBelow (r i) a c) b a = true
      rw [relOf_iff, insB_t (r i) a c b (Ne.symm hab), insB_b]
      omega
  have h₂ : S.f P' c a = true := by
    apply S.hf.unanimity P' hP'
    intro i
    show relOf (insertBelow (r i) a c) c a = true
    rw [relOf_iff, insB_t (r i) a c c (Ne.symm hac), insB_b]
    omega
  have h₃ : S.f P' c b = true := ord_trans (S.hf.ordering P' hP') h₂ h₁
  have e : S.f P c b = S.f P' c b :=
    S.hf.pairwise P P' hP hP' c b
      (fun i => (agree (r i) _ (P i) (hr i) c b
        (insB_t (r i) a c c (Ne.symm hac)) (insB_t (r i) a c b (Ne.symm hab))).symm)
      (fun i => (agree (r i) _ (P i) (hr i) b c
        (insB_t (r i) a c b (Ne.symm hab)) (insB_t (r i) a c c (Ne.symm hac))).symm)
  rw [e]
  exact h₃

omit [DecidableEq I] in
/-- Decisive for one pair implies decisive for every pair. -/
theorem expand (S : Setting X I) (G : I → Bool) (x y : X) (hW : W S G x y) (hxy : x ≠ y) :
    ∀ u v, u ≠ v → W S G u v := by
  have hx : ∀ v, v ≠ x → W S G x v := by
    intro v hv
    by_cases hvy : v = y
    · rw [hvy]
      exact hW
    · exact expandRight S G x y v hW hxy hvy
  have hy : ∀ u, u ≠ y → W S G u y := by
    intro u hu
    by_cases hux : u = x
    · rw [hux]
      exact hW
    · exact expandLeft S G x y u hW (Ne.symm hux) hxy
  intro u v huv
  by_cases hux : u = x
  · rw [hux] at huv ⊢
    exact hx v (Ne.symm huv)
  · by_cases hvx : v = x
    · rw [hvx] at huv ⊢
      by_cases huy : u = y
      · rw [huy]
        obtain ⟨w, hwx, hwy⟩ := third S x y
        have h₁ : W S G x w := hx w hwx
        have h₂ : W S G y w := expandLeft S G x w y h₁ hxy (Ne.symm hwx)
        exact expandRight S G y w x h₂ (Ne.symm hwy) (Ne.symm hwx)
      · exact expandRight S G u y x (hy u huy) huy hxy
    · exact expandLeft S G x v u (hx v hvx) (Ne.symm hux) (Ne.symm hvx)

/-! ### (3) Contraction -/

omit [DecidableEq X] [DecidableEq I] in
/-- One profile pattern on (x, y) settles decisiveness of G for (x, y). -/
theorem pattern (S : Setting X I) (P₀ : I → Rel X) (hP₀ : ∀ i, IsOrdering (P₀ i))
    (G : I → Bool) (x y : X)
    (hG : ∀ i, G i = true → P₀ i x y = true) (hO : ∀ i, G i = false → P₀ i y x = true)
    (hf : S.f P₀ x y = true) : W S G x y := by
  intro P hP hG' hO'
  have a₁ : ∀ i, P i x y = P₀ i x y := by
    intro i
    cases hg : G i with
    | true => rw [hG' i hg, hG i hg]
    | false => rw [(hP i).asymm y x (hO' i hg), (hP₀ i).asymm y x (hO i hg)]
  have a₂ : ∀ i, P i y x = P₀ i y x := by
    intro i
    cases hg : G i with
    | true => rw [(hP i).asymm x y (hG' i hg), (hP₀ i).asymm x y (hG i hg)]
    | false => rw [hO' i hg, hO i hg]
  rw [S.hf.pairwise P P₀ hP hP₀ x y a₁ a₂]
  exact hf

/-- The ranking a, b, c (everything else below). -/
def rk3 (a b c : X) : X → Nat :=
  fun t => if t = a then 0 else if t = b then 1 else if t = c then 2 else 3

theorem rk3_rel (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    relOf (rk3 a b c) a b = true ∧ relOf (rk3 a b c) a c = true ∧
    relOf (rk3 a b c) b c = true := by
  simp [relOf, rk3, Ne.symm hab, Ne.symm hac, Ne.symm hbc]

/-- G₁ ranks x y z, G₂ ranks y z x, everyone else z x y. -/
def contrProfile (G₁ G₂ : I → Bool) (x y z : X) : I → Rel X :=
  fun i => relOf (if G₁ i = true then rk3 x y z else if G₂ i = true then rk3 y z x else rk3 z x y)

omit [DecidableEq I] in
/-- If a decisive coalition is split into two parts, one part is decisive. -/
theorem contract (S : Setting X I) (G G₁ G₂ : I → Bool)
    (hW : ∀ u v, u ≠ v → W S G u v)
    (hsplit : ∀ i, G i = (G₁ i || G₂ i)) (hdisj : ∀ i, G₁ i = true → G₂ i = false)
    (x y z : X) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (∀ u v, u ≠ v → W S G₁ u v) ∨ (∀ u v, u ≠ v → W S G₂ u v) := by
  let P₀ := contrProfile G₁ G₂ x y z
  have hP₀ : ∀ i, IsOrdering (P₀ i) := fun i => relOf_ord _
  have A := rk3_rel x y z hxy hxz hyz
  have B := rk3_rel y z x hyz (Ne.symm hxy) (Ne.symm hxz)
  have C := rk3_rel z x y (Ne.symm hxz) (Ne.symm hyz) hxy
  have g₁ : ∀ i, G₁ i = true → P₀ i = relOf (rk3 x y z) := by
    intro i h
    show contrProfile G₁ G₂ x y z i = _
    simp [contrProfile, h]
  have g₂ : ∀ i, G₁ i = false → G₂ i = true → P₀ i = relOf (rk3 y z x) := by
    intro i h h'
    show contrProfile G₁ G₂ x y z i = _
    simp [contrProfile, h, h']
  have g₃ : ∀ i, G₁ i = false → G₂ i = false → P₀ i = relOf (rk3 z x y) := by
    intro i h h'
    show contrProfile G₁ G₂ x y z i = _
    simp [contrProfile, h, h']
  -- G puts y above z, everyone else z above y: f puts y above z.
  have fyz : S.f P₀ y z = true := by
    apply hW y z hyz P₀ hP₀
    · intro i hi
      cases h₁ : G₁ i with
      | true =>
        rw [g₁ i h₁]
        exact A.2.2
      | false =>
        have h₂ : G₂ i = true := by
          rw [hsplit i, h₁] at hi
          simpa using hi
        rw [g₂ i h₁ h₂]
        exact B.1
    · intro i hi
      have hb : G₁ i = false ∧ G₂ i = false := by
        rw [hsplit i] at hi
        simpa using hi
      rw [g₃ i hb.1 hb.2]
      exact C.2.1
  cases hxz' : S.f P₀ x z with
  | true =>
    left
    -- only G₁ puts x above z
    have w₁ : W S G₁ x z := pattern S P₀ hP₀ G₁ x z
      (fun i h₁ => by
        rw [g₁ i h₁]
        exact A.2.1)
      (fun i h₁ => by
        cases h₂ : G₂ i with
        | true =>
          rw [g₂ i h₁ h₂]
          exact B.2.2
        | false =>
          rw [g₃ i h₁ h₂]
          exact C.1)
      hxz'
    exact expand S G₁ x z w₁ hxz
  | false =>
    right
    have fyx : S.f P₀ y x = true := by
      rcases (S.hf.ordering P₀ hP₀).negTrans y x z fyz with h | h
      · exact h
      · rw [hxz'] at h
        cases h
    -- only G₂ puts y above x
    have w₂ : W S G₂ y x := pattern S P₀ hP₀ G₂ y x
      (fun i h₂ => by
        have h₁ : G₁ i = false := by
          cases h : G₁ i with
          | false => rfl
          | true =>
            have := hdisj i h
            rw [this] at h₂
            cases h₂
        rw [g₂ i h₁ h₂]
        exact B.2.1)
      (fun i h₂ => by
        cases h₁ : G₁ i with
        | true =>
          rw [g₁ i h₁]
          exact A.1
        | false =>
          rw [g₃ i h₁ h₂]
          exact C.2.2)
      fyx
    exact expand S G₂ y x w₂ (Ne.symm hxy)

/-! ### (5) A decisive single voter is a dictator -/

theorem dictator_of_W (S : Setting X I) (k : I)
    (hk : ∀ u v, u ≠ v → W S (fun i => decide (i = k)) u v) :
    ∀ P : I → Rel X, (∀ i, IsOrdering (P i)) → ∀ x y, P k x y = true → S.f P x y = true := by
  intro P hP x y hxy
  obtain ⟨w, hwx, hwy⟩ := third S x y
  obtain ⟨r, hr⟩ : ∃ r : I → X → Nat, ∀ i s t, P i s t = true ↔ r i s < r i t :=
    ⟨fun i => above S.allX (P i), fun i s t => rank_spec S.allX S.hallX (P i) (hP i) s t⟩
  have hxyk := (hr k x y).mp hxy
  -- voter k: w just below x; everyone else: w on top
  let P' : I → Rel X := fun i =>
    relOf (if i = k then insertBelow (r i) w x else putTop (r i) w)
  have hP' : ∀ i, IsOrdering (P' i) := fun i => relOf_ord _
  have h₁ : S.f P' x w = true := by
    apply hk x w (Ne.symm hwx) P' hP'
    · intro i hi
      have e : i = k := of_decide_eq_true hi
      rw [e]
      show relOf (if k = k then insertBelow (r k) w x else putTop (r k) w) x w = true
      rw [ite_eq_left rfl, relOf_iff, insB_t (r k) w x x (Ne.symm hwx), insB_b]
      omega
    · intro i hi
      have e : i ≠ k := of_decide_eq_false hi
      show relOf (if i = k then insertBelow (r i) w x else putTop (r i) w) w x = true
      rw [ite_eq_right e, relOf_iff, top_b, top_t (r i) w x (Ne.symm hwx)]
      omega
  have h₂ : S.f P' w y = true := by
    apply S.hf.unanimity P' hP'
    intro i
    show relOf (if i = k then insertBelow (r i) w x else putTop (r i) w) w y = true
    by_cases e : i = k
    · have hxyi : r i x < r i y := by
        rw [e]
        exact hxyk
      rw [ite_eq_left e, relOf_iff, insB_b, insB_t (r i) w x y (Ne.symm hwy)]
      omega
    · rw [ite_eq_right e, relOf_iff, top_b, top_t (r i) w y (Ne.symm hwy)]
      omega
  have h₃ : S.f P' x y = true := ord_trans (S.hf.ordering P' hP') h₁ h₂
  have agr : ∀ s t, s ≠ w → t ≠ w → ∀ i, P i s t = P' i s t := by
    intro s t hs ht i
    show P i s t = relOf (if i = k then insertBelow (r i) w x else putTop (r i) w) s t
    by_cases e : i = k
    · rw [ite_eq_left e]
      exact (agree (r i) _ (P i) (hr i) s t
        (insB_t (r i) w x s hs) (insB_t (r i) w x t ht)).symm
    · rw [ite_eq_right e]
      exact (agree (r i) _ (P i) (hr i) s t
        (top_t (r i) w s hs) (top_t (r i) w t ht)).symm
  have e : S.f P x y = S.f P' x y :=
    S.hf.pairwise P P' hP hP' x y (agr x y (Ne.symm hwx) (Ne.symm hwy))
      (agr y x (Ne.symm hwy) (Ne.symm hwx))
  rw [e]
  exact h₃

/-! ### (4) Shrinking to a single voter -/

theorem shrink (S : Setting X I) :
    ∀ (L : List I) (G : I → Bool), (∀ i, G i = true → i ∈ L) →
      (∀ u v, u ≠ v → W S G u v) → ∃ k, ∀ u v, u ≠ v → W S (fun i => decide (i = k)) u v
  | [], G, hL, hW => by
    exfalso
    let P : I → Rel X := fun _ => relOf (fun t => if t = S.b then 0 else 1)
    have hP : ∀ i, IsOrdering (P i) := fun _ => relOf_ord _
    have hba : ∀ i, P i S.b S.a = true := by
      intro i
      show relOf (fun t => if t = S.b then 0 else 1) S.b S.a = true
      rw [relOf_iff]
      simp [S.hab]
    have h₁ : S.f P S.a S.b = true :=
      hW S.a S.b S.hab P hP
        (fun i hi => by
          have := hL i hi
          cases this)
        (fun i _ => hba i)
    have h₂ : S.f P S.b S.a = true := S.hf.unanimity P hP S.b S.a hba
    have h₃ := (S.hf.ordering P hP).asymm S.a S.b h₁
    rw [h₂] at h₃
    cases h₃
  | k :: L, G, hL, hW => by
    cases hk : G k with
    | false =>
      apply shrink S L G _ hW
      intro i hi
      rcases List.mem_cons.mp (hL i hi) with e | e
      · rw [e, hk] at hi
        cases hi
      · exact e
    | true =>
      have hs : ∀ i, G i = (decide (i = k) || (G i && !decide (i = k))) := by
        intro i
        by_cases e : i = k
        · rw [e, hk]
          simp
        · simp [e]
      have hd : ∀ i, decide (i = k) = true → (G i && !decide (i = k)) = false := by
        intro i h
        have e : i = k := of_decide_eq_true h
        rw [e]
        simp
      rcases contract S G (fun i => decide (i = k)) (fun i => G i && !decide (i = k))
          hW hs hd S.a S.b S.c S.hab S.hac S.hbc with h | h
      · exact ⟨k, h⟩
      · apply shrink S L _ _ h
        intro i hi
        have hne : i ≠ k := by
          intro e
          rw [e] at hi
          simp at hi
        have hGi : G i = true := by
          cases hg : G i with
          | true => rfl
          | false =>
            rw [hg] at hi
            simp at hi
        rcases List.mem_cons.mp (hL i hGi) with e | e
        · exact absurd e hne
        · exact e

/-! ### Arrow's theorem -/

/-- Arrow's theorem (as stated in Gibbard 1973): a social welfare function
    on at least three outcomes satisfying Unanimity and Pairwise
    Determination has a dictator. -/
theorem arrow (S : Setting X I) (allI : List I) (hallI : ∀ i, i ∈ allI) :
    ∃ k, ∀ P : I → Rel X, (∀ i, IsOrdering (P i)) →
      ∀ x y, P k x y = true → S.f P x y = true := by
  have hN : ∀ u v, u ≠ v → W S (fun _ => true) u v := by
    intro u v _ P hP hG _
    exact S.hf.unanimity P hP u v (fun i => hG i rfl)
  obtain ⟨k, hk⟩ := shrink S allI (fun _ => true) (fun i _ => hallI i) hN
  exact ⟨k, dictator_of_W S k hk⟩

end Arrow

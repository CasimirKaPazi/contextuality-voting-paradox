/-
  The topology of Condorcet's paradox for three alternatives, done
  combinatorially (Livson, Pritam, Prokopenko, "The non-orientable topology
  of Condorcet's paradox", arXiv:2601.07283).

  Everything here is finite and checked by computation (`decide +kernel`).
  Uses only core Lean, no Mathlib.

  What is proved:
  * Baryshnikov's nerve N(U) has 6 triangles and 12 edges, and its edges
    lying in only one triangle are exactly the edges of the two preference
    cycles (so the cycles are its two boundary circles).
  * Of the six ways to glue one boundary cycle onto the other, the three that
    respect the reference orientations (Definition 5) give a non-orientable
    closed surface, and the three that reverse them give an orientable one.
    With χ = 3 − 9 + 6 = 0 these are the Klein bottle and the torus.
    The gluing ij ↦ ji (reverse every preference) is one of the orientable ones.
  * N(V), the nerve with both cycles filled in, is a closed orientable surface
    with χ = 6 − 12 + 8 = 2 (a sphere).
  * Identifying only the two filled-in cycle triangles does not give a surface:
    each glued edge then lies in three triangles.
  * Reversing every preference (ij ↦ ji) is a free, orientation-reversing
    symmetry of N(V). The quotient is closed, non-orientable, χ = 2/2 = 1.

  What is not proved here, and rests on standard topology outside this file:
  * that combinatorial orientability (a coherent choice of triangle
    orientations) agrees with topological orientability;
  * the classification of closed surfaces, which turns
    "closed, χ = 0, non-orientable" into "Klein bottle" and
    "closed, χ = 1, non-orientable" into "real projective plane".
-/

set_option maxRecDepth 100000

namespace Nerve

/-- Vertices of Baryshnikov's nerve: `vij` is the covering set U_ij,
    the strict orders in which i is preferred to j. -/
inductive Vtx where
  | v12 | v13 | v21 | v23 | v31 | v32
  deriving DecidableEq, Repr

open Vtx

def allV : List Vtx := [v12, v13, v21, v23, v31, v32]

/-- The six triangles of N(U), one per strict order a ≺ b ≺ c, each written
    in its reference orientation [ab, bc, ac] (Definition 4). -/
def tris : List (List Vtx) :=
  [ [v12, v23, v13],   -- 1 ≺ 2 ≺ 3
    [v13, v32, v12],   -- 1 ≺ 3 ≺ 2
    [v21, v13, v23],   -- 2 ≺ 1 ≺ 3
    [v23, v31, v21],   -- 2 ≺ 3 ≺ 1
    [v31, v12, v32],   -- 3 ≺ 1 ≺ 2
    [v32, v21, v31] ]  -- 3 ≺ 2 ≺ 1

/-- The two preference cycles, in reference orientation [ab, bc, ca]. -/
def cycleA : List Vtx := [v12, v23, v31]   -- 1 ≺ 2 ≺ 3 ≺ 1
def cycleB : List Vtx := [v13, v32, v21]   -- 1 ≺ 3 ≺ 2 ≺ 1

/-! ### The nerve N(U) is an annulus whose boundary is the two cycles -/

/-- Number of triangles containing both `u` and `v`. -/
def occ (ts : List (List Vtx)) (u v : Vtx) : Nat :=
  (ts.filter (fun t => t.contains u && t.contains v)).length

def inA (u v : Vtx) : Bool := cycleA.contains u && cycleA.contains v
def inB (u v : Vtx) : Bool := cycleB.contains u && cycleB.contains v

/-- Every edge lies in at most two triangles, and it lies in exactly one
    precisely when both endpoints belong to the same preference cycle. -/
theorem boundary_is_the_two_cycles :
    (allV.all fun u => allV.all fun v =>
      u == v ||
      (decide (occ tris u v ≤ 2) && ((occ tris u v == 1) == (inA u v || inB u v)))) = true := by
  decide +kernel

/-- Ordered pairs (u, v), u ≠ v, that span an edge; twice the number of edges. -/
def orderedEdges (ts : List (List Vtx)) : Nat :=
  allV.foldl (fun acc u =>
    allV.foldl (fun acc2 v =>
      if u != v && decide (0 < occ ts u v) then acc2 + 1 else acc2) acc) 0

/-- N(U) has 12 edges. -/
theorem annulus_edges : orderedEdges tris = 24 := by
  decide +kernel

/-! ### Orientations -/

/-- The directed edges of a triangle, in its listed orientation or flipped. -/
def dirEdges (t : List Vtx) (flip : Bool) : List (Vtx × Vtx) :=
  match t with
  | [x, y, z] => if flip then [(y, x), (z, y), (x, z)] else [(x, y), (y, z), (z, x)]
  | _ => []

/-- All directed edges, given one flip choice per triangle. -/
def allDir (ts : List (List Vtx)) (signs : List Bool) : List (Vtx × Vtx) :=
  (ts.zip signs).foldr (fun p acc => dirEdges p.1 p.2 ++ acc) []

def noDup : List (Vtx × Vtx) → Bool
  | [] => true
  | x :: xs => !xs.contains x && noDup xs

/-- All 2^n choices of flips for n triangles. -/
def allSigns : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allSigns n).map (false :: ·) ++ (allSigns n).map (true :: ·)

/-- An orientation is coherent when no directed edge occurs twice, i.e. the
    two triangles at every inner edge run along it in opposite directions. -/
def coherent (ts : List (List Vtx)) (signs : List Bool) : Bool :=
  noDup (allDir ts signs)

theorem annulus_orientable : ((allSigns 6).any fun s => coherent tris s) = true := by
  decide +kernel

/-! ### Gluing the two boundary cycles: Klein bottle or torus -/

/-- A gluing sends the vertices of cycle A to those of cycle B. -/
structure Gluing where
  img12 : Vtx
  img23 : Vtx
  img31 : Vtx
  deriving Repr

def Gluing.apply (g : Gluing) : Vtx → Vtx
  | .v12 => g.img12
  | .v23 => g.img23
  | .v31 => g.img31
  | v => v

/-- After gluing, a boundary edge (u, v) of cycle A and its image in cycle B
    are one edge, so the image must be traversed the other way:
    (g u, g v) must not occur. -/
def gluedOK (g : Gluing) (D : List (Vtx × Vtx)) : Bool :=
  D.all fun e => !(inA e.1 e.2) || !(D.contains (g.apply e.1, g.apply e.2))

/-- The glued surface admits a coherent orientation. -/
def orientable (g : Gluing) : Bool :=
  (allSigns 6).any fun s => coherent tris s && gluedOK g (allDir tris s)

/-- All six bijections from cycle A to cycle B. -/
def gluings : List Gluing :=
  [⟨v13, v32, v21⟩, ⟨v13, v21, v32⟩, ⟨v32, v13, v21⟩,
   ⟨v32, v21, v13⟩, ⟨v21, v13, v32⟩, ⟨v21, v32, v13⟩]

/-- Successor in the reference orientation of cycle B: 13 → 32 → 21 → 13. -/
def nextB : Vtx → Vtx
  | .v13 => .v32
  | .v32 => .v21
  | .v21 => .v13
  | v => v

/-- The gluing carries the reference orientation 12 → 23 → 31 of cycle A
    to the reference orientation of cycle B. -/
def respectsReference (g : Gluing) : Bool :=
  nextB g.img12 == g.img23 && nextB g.img23 == g.img31 && nextB g.img31 == g.img12

/-- The gluing of Definition 5: identify the cycles along their reference
    orientations. -/
def referenceGluing : Gluing := ⟨v13, v32, v21⟩

/-- Reverse every preference: ij ↦ ji. -/
def reversalGluing : Gluing := ⟨v21, v32, v13⟩

/-- Theorem 4, combinatorial part: the reference gluing is non-orientable. -/
theorem reference_gluing_nonorientable : orientable referenceGluing = false := by
  decide +kernel

/-- The reversal gluing is orientable (a torus). -/
theorem reversal_gluing_orientable : orientable reversalGluing = true := by
  decide +kernel

/-- All six gluings: non-orientable exactly when they respect the reference
    orientations. -/
theorem six_gluings :
    (gluings.all fun g => orientable g == !respectsReference g) = true := by
  decide +kernel

/-- Where orientation is lost (Proposition 5 of *Cycles, Twists and Walls*).
    Fix a coherent orientation of the annulus. Under a gluing that respects the
    reference orientations, every seam edge joins two triangles whose
    orientations disagree (the image edge is traversed the same way); under the
    other three gluings, none does. -/
theorem seam :
    (gluings.all fun g => (allSigns 6).all fun s =>
      !coherent tris s ||
      ((allDir tris s).filter (fun e => inA e.1 e.2)).all fun e =>
        (allDir tris s).contains (g.apply e.1, g.apply e.2) == respectsReference g) = true := by
  decide +kernel

/-! ### Realised cycles: the sphere N(V) and the projective plane -/

/-- N(V): N(U) with both preference cycles filled in. -/
def trisV : List (List Vtx) := tris ++ [cycleA, cycleB]

/-- N(V) is closed: every edge lies in exactly two triangles. -/
theorem sphere_closed :
    (allV.all fun u => allV.all fun v =>
      u == v || occ trisV u v == 0 || occ trisV u v == 2) = true := by
  decide +kernel

/-- N(V) still has 12 edges, so χ = 6 − 12 + 8 = 2. -/
theorem sphere_edges : orderedEdges trisV = 24 := by
  decide +kernel

theorem sphere_orientable : ((allSigns 8).any fun s => coherent trisV s) = true := by
  decide +kernel

def edgesA : List (Vtx × Vtx) := [(v12, v23), (v23, v31), (v31, v12)]

/-- Identifying only the two cycle triangles of N(V), by any of the six
    gluings: each glued edge lies in one annulus triangle on the A side, one
    on the B side, and the shared cycle triangle. Three triangles meet at one
    edge, so the result is not a surface. -/
theorem gluing_caps_only_is_not_a_surface :
    (gluings.all fun g => edgesA.all fun e =>
      occ tris e.1 e.2 + occ tris (g.apply e.1) (g.apply e.2) + 1 == 3) = true := by
  decide +kernel

/-- Reverse every preference. -/
def rev : Vtx → Vtx
  | .v12 => .v21
  | .v21 => .v12
  | .v13 => .v31
  | .v31 => .v13
  | .v23 => .v32
  | .v32 => .v23

def sameTri (t1 t2 : List Vtx) : Bool :=
  t1.all (fun x => t2.contains x) && t2.all (fun x => t1.contains x)

/-- `rev` is a free symmetry of N(V): it fixes no vertex, no edge and no
    triangle, and maps triangles to triangles. -/
theorem rev_free_symmetry :
    (allV.all (fun v => rev v != v) &&
     (allV.all fun u => allV.all fun v => rev u != v || occ trisV u v == 0) &&
     (trisV.all fun t =>
        trisV.any (fun t' => sameTri (t.map rev) t') && !sameTri (t.map rev) t)) = true := by
  decide +kernel

/-- `rev` reverses every coherent orientation of N(V). Hence the quotient
    N(V)/rev is a closed non-orientable surface with χ = 2/2 = 1. -/
theorem rev_reverses_orientation :
    ((allSigns 8).all fun s =>
      !coherent trisV s ||
      (allDir trisV s).all (fun e => (allDir trisV s).contains (rev e.2, rev e.1))) = true := by
  decide +kernel

end Nerve

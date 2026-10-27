/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.LGV2.Part29
import Theorem.LinearAlgebra.Matrix.Determinant.LGV1.Part8
open Finset BigOperators Matrix

/-!
# The Lindström-Gessel-Viennot Lemma: Part 1

This file formalizes the first part of the Lindström-Gessel-Viennot (LGV) lemma,
covering the basic definitions and counting results for lattice paths.

## Main definitions

* `LGV1.LatticePoint` - A point on the integer lattice ℤ²
* `LGV1.integerLattice` - The integer lattice as a Mathlib `Digraph`
* `LGV1.LatticePath` - A path on the integer lattice using only east (right) and north (up) steps
* `LGV1.LatticePath.stepCount` - The total number of steps in a path
* `LGV1.LatticePath.eastStepCount` - The number of east steps in a path
* `LGV1.PathTuple` - A k-tuple of lattice paths from k source vertices to k target vertices
* `LGV1.PathTuple.isNonIntersecting` - Property that no two paths share a vertex (nipat)
* `LGV1.PathTuple.isIntersecting` - Property that some two paths share a vertex (ipat)
* `LGV1.kVertex` - A k-tuple of lattice points

## Main results

* `latticePath_count` - Number of paths from (a,b) to (c,d) equals C(c+d-a-b, c-a)
  (Proposition prop.lgv.1-paths.ct)
* `lgv_two_paths` - LGV lemma for k=2: determinant equals #nipats to (B,B') - #nipats to (B',B)
  (Proposition prop.lgv.2paths.count)
* `baby_jordan_curve` - Paths from A to B' and A' to B must intersect under NW conditions
  (Proposition prop.lgv.jordan-2)
* `binom_log_concave` - C(n,k)² ≥ C(n,k-1)·C(n,k+1)
  (Corollary cor.lgv.binom-unimod)
* `lgv_k_paths` - General LGV lemma: determinant equals signed sum of nipat counts
  (Proposition prop.lgv.kpaths.count)

## References

* Source: AlgebraicCombinatorics/tex/Determinants/LGV1.tex (sec.det.comb.lgv)

## Implementation notes

We formalize lattice paths as lists of steps (east or north), rather than as sequences
of vertices. This makes it easier to work with path concatenation and step counting.

The LGV lemma relates determinants to non-intersecting lattice paths. The key insight
is a sign-reversing involution that cancels intersecting path tuples.

### Relationship with LGV2.lean

This file (LGV1.lean) and LGV2.lean both work with the integer lattice digraph, but
use different representations:

- **LGV1.lean**: Uses Mathlib's `Digraph` type and `LatticePath` (list of steps: east/north)
- **LGV2.lean**: Uses `LGV.SimpleDigraph` (custom structure with irreflexivity) and
  `SimpleDigraph.Path` (list of vertices)

The integer lattice definitions have equivalent adjacency relations:
- LGV1: `integerLattice_adj_iff p q : integerLattice.Adj p q ↔ q = (p.1 + 1, p.2) ∨ q = (p.1, p.2 + 1)`
- LGV2: `integerLattice_arc_iff u v : integerLattice.arc u v ↔ v = (u.1 + 1, u.2) ∨ v = (u.1, u.2 + 1)`

### LatticeStep and LatticePath equivalence

Both files define a `LatticeStep` type for representing east/north steps:
- `LGV1.LatticeStep` (this file)
- `LGV.LatticeStep'` (in LGV2.lean)

These are equivalent types, with explicit conversion functions:
- `latticeStepEquiv : LatticeStep ≃ LGV.LatticeStep'`
- `latticePathToLatticePath' : LatticePath → LGV.LatticePath'`
- `latticePath'ToLatticePath : LGV.LatticePath' → LatticePath`

The duplication exists because LGV1 imports LGV2, preventing LGV2 from referencing
LGV1's definitions. Both definitions are kept compatible with trivial conversions.

LGV2.lean contains the complete weighted LGV lemma proof. This file contains the
counting case infrastructure with lattice-specific path counting results.
-/


namespace LGV1

/-!
## Baby Jordan Curve Theorem (Proposition prop.lgv.jordan-2)

If A' is weakly northwest of A, and B' is weakly northwest of B,
then any path from A to B' must intersect any path from A' to B.

This means:
- x(A') ≤ x(A) and y(A') ≥ y(A)
- x(B') ≤ x(B) and y(B') ≥ y(B)

Under these conditions, #nipats from (A,A') to (B',B) = 0.
-/


/-- Point p is weakly northwest of point q. -/
def isWeaklyNorthwestOf (p q : LatticePoint) : Prop :=
  p.x ≤ q.x ∧ p.y ≥ q.y

/-!
## Log-Concavity of Binomial Coefficients (Corollary cor.lgv.binom-unimod)

As an application of the LGV lemma:
C(n,k)² ≥ C(n,k-1) · C(n,k+1)

This follows by choosing appropriate lattice points and applying
Propositions prop.lgv.2paths.count and prop.lgv.jordan-2.
-/
/-!
## The LGV Lemma for k Paths (Proposition prop.lgv.kpaths.count)

For k-vertices A = (A₁, ..., Aₖ) and B = (B₁, ..., Bₖ):

det(#paths from Aᵢ to Bⱼ)_{i,j} = ∑_{σ ∈ Sₖ} (-1)^σ · #nipats from A to σ(B)

The proof generalizes the k=2 case by using a sign-reversing involution
that picks the first pair of intersecting paths and exchanges their tails.
-/
/-! ### Helper lemmas for the product rule -/

/-- Equivalence between PathTuple and subtype of functions. -/
def PathTuple.equivSubtype {k : ℕ} (A B : kVertex k) :
    PathTuple k A B ≃ { f : Fin k → LatticePath // ∀ i, f i ∈ pathsFromTo (A i) (B i) } where
  toFun pt := ⟨pt.paths, pt.valid⟩
  invFun sf := ⟨sf.val, sf.property⟩
  left_inv pt := by cases pt; rfl
  right_inv sf := by cases sf; rfl

/-- The path count matrix for k source and target vertices. -/
def pathMatrixK {k : ℕ} (A B : kVertex k) : Matrix (Fin k) (Fin k) ℤ :=
  Matrix.of fun i j => numPaths (A i) (B j)

/-- Number of nipats from A to σ(B).
    Defined as the cardinality of the set of non-intersecting path tuples. -/
noncomputable def numNipatsK {k : ℕ} (A B : kVertex k) (σ : Equiv.Perm (Fin k)) : ℕ :=
  (nipatsFromTo A (B.permute σ)).ncard

/-- Number of ipats from A to σ(B).
    Defined as the cardinality of the set of intersecting path tuples. -/
noncomputable def numIpatsK {k : ℕ} (A B : kVertex k) (σ : Equiv.Perm (Fin k)) : ℕ :=
  (ipatsFromTo A (B.permute σ)).ncard

/-!
### Bridge to LGV2.lean

We establish the connection between LGV1's path representation and LGV2's.
The key observation is that both represent the same mathematical objects.

The bridge uses the following chain of equivalences:
1. LGV1.LatticeStep ≃ LGV.LatticeStep' (both are {east, north})
2. LGV1.LatticePath ≃ LGV.LatticePath' (both are lists of steps)
3. LGV1.PathTuple k A B ≃ LGV.LatticePath'Tuple k A B (same structure)
4. LGV.LatticePath'Tuple k A B ≃ LGV.PathTuple integerLattice k A B (via latticePath'TupleEquiv)

The intersection property is preserved at each step, so:
- ipatsFromTo A B ≃ ipatSet integerLattice A B
- numIpatsK A B σ = (ipatFinset ... A (permuteKVertex σ B)).card
-/


/-- Equivalence between `LGV1.LatticeStep` and `LGV.LatticeStep'`.
    
    This is a definitional equivalence: both types have the same structure
    (two constructors `east` and `north`), so the equivalence is trivial.
    The equivalence preserves the `apply` function: `latticeStepEquiv_apply`. -/
def latticeStepEquiv : LatticeStep ≃ LGV.LatticeStep' where
  toFun s := match s with
    | LatticeStep.east => LGV.LatticeStep'.east
    | LatticeStep.north => LGV.LatticeStep'.north
  invFun s := match s with
    | LGV.LatticeStep'.east => LatticeStep.east
    | LGV.LatticeStep'.north => LatticeStep.north
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl

end LGV1

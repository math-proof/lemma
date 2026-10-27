/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.LGV2.Part29
import Theorem.LinearAlgebra.Matrix.Determinant.LGV1.Part4
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

noncomputable def PathTuple.minCrowdedPathIndex {k : ℕ} {A B : kVertex k} 
    (pt : PathTuple k A B) (hip : pt.isIntersecting) : Fin k :=
  (pt.crowdedPathIndices.min' (pt.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip))

/-- The crowded vertices on a specific path: vertices that appear in multiple paths -/
def PathTuple.crowdedVerticesOnPath {k : ℕ} {A B : kVertex k} 
    (pt : PathTuple k A B) (i : Fin k) : Set LatticePoint :=
  { v | v ∈ pt.verticesOf i ∧ ∃ j : Fin k, i ≠ j ∧ v ∈ pt.verticesOf j }

/-- A path tuple with permutation: pairs (σ, pt) where pt is a path tuple from A to σ(B) -/
def pathTupleWithPerm {k : ℕ} (A B : kVertex k) : Type :=
  (σ : Equiv.Perm (Fin k)) × PathTuple k A (B.permute σ)

/-- The sign of a path tuple with permutation -/
def signOfPathTupleWithPerm {k : ℕ} {A B : kVertex k} (sp : pathTupleWithPerm A B) : ℤ :=
  Equiv.Perm.sign sp.1

/-- The set of all ipats with permutation -/
def ipatWithPerm {k : ℕ} (A B : kVertex k) : Set (pathTupleWithPerm A B) :=
  { sp | sp.2.isIntersecting }

/-!
## The LGV Lemma for Two Paths (Proposition prop.lgv.2paths.count)

For two 2-vertices (A, A') and (B, B'):

det | #paths(A→B)   #paths(A→B')  |
    | #paths(A'→B)  #paths(A'→B') |

= #nipats from (A,A') to (B,B') - #nipats from (A,A') to (B',B)

The proof uses a sign-reversing involution on intersecting path tuples
that exchanges the tails of two intersecting paths.
-/


/-- The path count matrix for two source and target points. -/
def pathMatrix2 (A A' B B' : LatticePoint) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![numPaths A B, numPaths A B';
     numPaths A' B, numPaths A' B']

/-- Number of nipats from (A,A') to (B,B').
    Defined as the cardinality of the set of non-intersecting path tuples. -/
noncomputable def numNipats2 (A A' B B' : LatticePoint) : ℕ :=
  let AB : kVertex 2 := ![A, A']
  let BB : kVertex 2 := ![B, B']
  (nipatsFromTo AB BB).ncard

end LGV1

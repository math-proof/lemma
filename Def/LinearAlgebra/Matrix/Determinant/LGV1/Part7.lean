/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.LGV2.Part29
import Structure.LinearAlgebra.Matrix.Determinant.LGV1
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

/-- The set of vertices visited by a path in a path tuple. -/
def PathTuple.verticesOf {k : ℕ} {A B : kVertex k} (pt : PathTuple k A B)
    (i : Fin k) : Set LatticePoint :=
  { p | p ∈ (pt.paths i).vertices (A i) }

/-- A path tuple is non-intersecting (nipat) if no two distinct paths share a vertex.
    Label: def.lgv.path-tups (d) -/
def PathTuple.isNonIntersecting {k : ℕ} {A B : kVertex k} (pt : PathTuple k A B) : Prop :=
  ∀ i j, i ≠ j → Disjoint (pt.verticesOf i) (pt.verticesOf j)

/-- A path tuple is intersecting (ipat) if it is not non-intersecting.
    Label: def.lgv.path-tups (e) -/
def PathTuple.isIntersecting {k : ℕ} {A B : kVertex k} (pt : PathTuple k A B) : Prop :=
  ¬pt.isNonIntersecting

/-- The set of all path tuples from A to B. -/
def pathTuplesFromTo {k : ℕ} (A B : kVertex k) : Set (PathTuple k A B) :=
  Set.univ

/-- The set of all non-intersecting path tuples (nipats) from A to B. -/
def nipatsFromTo {k : ℕ} (A B : kVertex k) : Set (PathTuple k A B) :=
  { pt | pt.isNonIntersecting }

/-- The set of all intersecting path tuples (ipats) from A to B. -/
def ipatsFromTo {k : ℕ} (A B : kVertex k) : Set (PathTuple k A B) :=
  { pt | pt.isIntersecting }

/-!
## General k Involution Infrastructure

The sign-reversing involution for general k path tuples works as follows:
Given an intersecting path tuple (ipat), we:
1. Find the smallest path index i that contains a "crowded" vertex (shared with another path)
2. Find the first crowded vertex v on path i (by position in the path)
3. Find the largest path index j that contains v (j > i since v is crowded)
4. Exchange the tails of paths i and j at v
5. Compose σ with the transposition (i j) to flip the sign

This maps (σ, ipat) to (σ * swap(i,j), ipat') where:
- sign(σ * swap(i,j)) = -sign(σ) (transposition flips sign)
- ipat' is still intersecting (v is still a crowded point)
- The involution is its own inverse (applying twice returns the original)

Since every ipat has at least one crowded point, the involution has no fixed points.
-/


/-- A vertex is crowded in a path tuple if it appears in at least two paths -/
def PathTuple.isCrowded {k : ℕ} {A B : kVertex k} (pt : PathTuple k A B) (v : LatticePoint) : Prop :=
  ∃ i j : Fin k, i ≠ j ∧ v ∈ pt.verticesOf i ∧ v ∈ pt.verticesOf j

end LGV1

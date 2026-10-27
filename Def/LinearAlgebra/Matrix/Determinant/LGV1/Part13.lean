/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.LGV2.Part29
import Theorem.LinearAlgebra.Matrix.Determinant.LGV1.Part7
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

/-- The sign-reversing involution on intersecting signed path tuples.
    Given an ipat, we:
    1. Find the first intersection point v (deterministically, by index in path0)
    2. Exchange the tails of the two paths at v
    3. Flip the sign (swap toBB')

    This maps ipats to (B,B') ↔ ipats to (B',B).

    Note: We use `firstIntersection` instead of `Classical.choose` to ensure the
    involution is truly involutive. The key property is that after swapping tails,
    the same point v is still the first intersection point. -/
noncomputable def ipatInvolution {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B')
    (h : spt.isIntersecting) : SignedPathTuple2 A A' B B' :=
  -- Get the first intersection point (deterministic choice)
  let v := firstIntersection spt h
  let hv0 := firstIntersection_mem_path0 spt h
  let hv1 := firstIntersection_mem_path1 spt h
  -- Get the indices where v occurs in each path's vertices
  let idx0 := (spt.path0.vertices A).findIdx (· == v)
  let idx1 := (spt.path1.vertices A').findIdx (· == v)
  -- Split both paths at v: (head, tail) where head ends at v and tail starts at v
  let head0 := spt.path0.take idx0
  let tail0 := spt.path0.drop idx0
  let head1 := spt.path1.take idx1
  let tail1 := spt.path1.drop idx1
  -- Create new paths by exchanging tails
  let newPath0 := head0 ++ tail1
  let newPath1 := head1 ++ tail0
  -- The new path tuple has flipped sign
  { path0 := newPath0
    path1 := newPath1
    toBB' := !spt.toBB'
    valid0 := by
      -- newPath0 = head0 ++ tail1 goes A → v → (dest of path1)
      -- where dest of path1 = (if spt.toBB' then B' else B)
      -- and (if !spt.toBB' then B else B') = (if spt.toBB' then B' else B)
      show LatticePath.isPathFromTo newPath0 A (if !spt.toBB' then B else B')
      -- head0 goes A → v (by splitPathAt_head_endpoint)
      have hhead0 : LatticePath.isPathFromTo head0 A v :=
        splitPathAt_head_endpoint spt.path0 A v hv0
      -- path1 goes A' → (if spt.toBB' then B' else B)
      -- so tail1 = path1.drop idx1 goes v → (if spt.toBB' then B' else B)
      have hsplit1 := LatticePath.isPathFromTo_take_drop spt.path1 idx1 A' (if spt.toBB' then B' else B) spt.valid1
      have hhead1_eq_v : LatticePath.endpoint head1 A' = v :=
        splitPathAt_head_endpoint spt.path1 A' v hv1
      simp only at hsplit1
      rw [hhead1_eq_v] at hsplit1
      have htail1 : LatticePath.isPathFromTo tail1 v (if spt.toBB' then B' else B) := hsplit1.2
      -- newPath0 = head0 ++ tail1 goes A → v → (if spt.toBB' then B' else B)
      have hconcat := LatticePath.isPathFromTo_append head0 tail1 A v
        (if spt.toBB' then B' else B) hhead0 htail1
      -- (if !spt.toBB' then B else B') = (if spt.toBB' then B' else B)
      convert hconcat using 1
      cases spt.toBB' <;> rfl
    valid1 := by
      -- newPath1 = head1 ++ tail0 goes A' → v → (dest of path0)
      -- where dest of path0 = (if spt.toBB' then B else B')
      -- and (if !spt.toBB' then B' else B) = (if spt.toBB' then B else B')
      show LatticePath.isPathFromTo newPath1 A' (if !spt.toBB' then B' else B)
      -- head1 goes A' → v (by splitPathAt_head_endpoint)
      have hhead1 : LatticePath.isPathFromTo head1 A' v :=
        splitPathAt_head_endpoint spt.path1 A' v hv1
      -- path0 goes A → (if spt.toBB' then B else B')
      -- so tail0 = path0.drop idx0 goes v → (if spt.toBB' then B else B')
      have hsplit0 := LatticePath.isPathFromTo_take_drop spt.path0 idx0 A (if spt.toBB' then B else B') spt.valid0
      have hhead0_eq_v : LatticePath.endpoint head0 A = v :=
        splitPathAt_head_endpoint spt.path0 A v hv0
      simp only at hsplit0
      rw [hhead0_eq_v] at hsplit0
      have htail0 : LatticePath.isPathFromTo tail0 v (if spt.toBB' then B else B') := hsplit0.2
      -- newPath1 = head1 ++ tail0 goes A' → v → (if spt.toBB' then B else B')
      have hconcat := LatticePath.isPathFromTo_append head1 tail0 A' v
        (if spt.toBB' then B else B') hhead1 htail0
      -- (if !spt.toBB' then B' else B) = (if spt.toBB' then B else B')
      convert hconcat using 1
      cases spt.toBB' <;> rfl
  }

def signedNipats2_true (A A' B B' : LatticePoint) : Set (SignedPathTuple2 A A' B B') :=
  { spt ∈ signedNipats2 A A' B B' | spt.toBB' = true }

/-- Define the subset with toBB' = false -/
def signedNipats2_false (A A' B B' : LatticePoint) : Set (SignedPathTuple2 A A' B B') :=
  { spt ∈ signedNipats2 A A' B B' | spt.toBB' = false }

end LGV1

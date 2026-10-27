/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.LGV2.Part22
open Finset BigOperators Matrix

/-!
# The Lindström-Gessel-Viennot Lemma: Weighted and Generalized Versions

This file formalizes the weighted version of the LGV lemma and related results,
following Section "The weighted version ... The nonpermutable case" (sec.det.comb.lgv)
of the Algebraic Combinatorics notes.

## Main definitions

* `LGV.SimpleDigraph`: A digraph structure with no self-loops (irreflexive adjacency)
* `LGV.SimpleDigraph.toDigraph`: Conversion to Mathlib's `Digraph` type
* `LGV.ArcWeight`: A weight function on arcs of a digraph
* `LGV.pathWeight`: The weight of a path (product of arc weights)
* `LGV.pathTupleWeight`: The weight of a path tuple (product of path weights)
* `LGV.pathWeightMatrix`: The matrix of sums of path weights between source/target vertices
* `LGV.catalanHankelMatrix`: The Hankel matrix of Catalan numbers

## Main results

* `LGV.lgv_weighted_lattice`: LGV lemma, lattice weight version (Theorem thm.lgv.kpaths.wt)
* `LGV.lgv_weighted_digraph`: LGV lemma, digraph weight version (Theorem thm.lgv.kpaths.wt-dg)
* `LGV.lgv_nonpermutable`: LGV lemma, nonpermutable lattice weight version
    (Corollary cor.lgv.kpaths.wt-np)
* `LGV.binom_det_nonneg`: Determinant of binomial coefficient matrix is nonnegative
    (Corollary cor.lgv.binom-det-nonneg)
* `LGV.catalan_hankel_det`: Hankel determinant of Catalan numbers equals 1
    (Corollary cor.lgv.catalan-hankel-det-0)
* `LGV.catalan_hankel_det_zero` through `LGV.catalan_hankel_det_seven`: Base cases proved
    by computation

## References

* Source: AlgebraicCombinatorics/tex/Determinants/LGV2.tex
* [Lindström, *On the vector representations of induced matroids*][Lindstrom73]
* [Gessel-Viennot, *Binomial determinants, paths, and hook length formulae*][GesVie85]

## Implementation notes

We formalize the LGV lemma for general path-finite acyclic digraphs, with the integer
lattice ℤ² as a special case. The key construction is a sign-reversing involution
on intersecting path tuples that exchanges tails at the first intersection point.

The nonpermutable case applies when the source and target vertices are "sorted" in
a way that prevents non-identity permutations from having non-intersecting path tuples.

For the Catalan Hankel determinant, we use Mathlib's `catalan` function and prove
the base cases (k = 0, 1, ..., 7) by direct computation using `native_decide`.
The general theorem uses the LGV lemma with Dyck paths.

### Relationship with LGV1.lean

This file (LGV2.lean) and LGV1.lean both work with the integer lattice digraph, but
use different representations:

- **LGV1.lean**: Uses Mathlib's `Digraph` type and `LatticePath` (list of steps: east/north)
- **LGV2.lean**: Uses `LGV.SimpleDigraph` (custom structure with irreflexivity) and
  `SimpleDigraph.Path` (list of vertices)

The integer lattice definitions have equivalent adjacency relations, proven by
`integerLattice_arc_iff` and `integerLattice_toDigraph_adj_iff`. The conversion
`SimpleDigraph.toDigraph` allows transferring results between the two representations.

This file contains the complete weighted LGV lemma proof. LGV1.lean contains the
counting case infrastructure with lattice-specific path counting results.
-/


namespace LGV

variable {V : Type*} [DecidableEq V] {K : Type*} [CommRing K]

variable {V : Type*} [DecidableEq V]

/-!
## Bridge Between LGV1 and LGV2 Path Representations

This section documents the connection between the path representations used in
LGV1.lean (list of steps) and LGV2.lean (list of vertices), and provides key
infrastructure for bridging them.

### Key Insight

A `LatticePath` (list of east/north steps) starting at point `A` can be converted to
a `SimpleDigraph.Path` by computing the list of vertices visited:
- `[east, north, east]` starting at `(0,0)` → `[(0,0), (1,0), (1,1), (2,1)]`

The conversion is bijective for paths between fixed endpoints.

### Status

The key theorem `sum_signed_ipatFinset_card_eq_zero` proves that the signed sum of
ipat counts is zero. To use this in LGV1.lean's `lgv_involution_cancellation`, we need:

```
numIpatsK A B σ = (ipatFinset integerLattice_pathFinite A (permuteKVertex σ B)).card
```

This requires showing that `ipatsFromTo` (LGV1) and `ipatFinset` (LGV2) have the same
cardinality, which follows from a bijection between the path tuple representations.

### Approach

The bijection works as follows:
1. Given a `LatticePath` (list of steps) starting at `A`, compute the vertex list
2. This vertex list forms a valid `SimpleDigraph.Path` in `integerLattice`
3. The map is injective because different step sequences give different vertex lists
4. The map is surjective because every `SimpleDigraph.Path` in `integerLattice`
   corresponds to a unique step sequence (each arc is either east or north)

The intersection property is preserved because both representations check if
any vertex appears in multiple paths of the tuple.
-/


/-- A lattice step on the integer lattice: either east (+1,0) or north (0,+1).
    
    This is the canonical definition for lattice steps. LGV1.lean defines an equivalent
    type `LGV1.LatticeStep` with an explicit equivalence `LGV1.latticeStepEquiv`.
    
    The two types are isomorphic via:
    - `LGV1.latticeStepEquiv : LGV1.LatticeStep ≃ LGV.LatticeStep'`
    - `LGV1.latticePathToLatticePath' : LGV1.LatticePath → LGV.LatticePath'`
    - `LGV1.latticePath'ToLatticePath : LGV.LatticePath' → LGV1.LatticePath`
    
    Note: The duplication exists because LGV1 imports LGV2, so LGV2 cannot reference
    LGV1's definitions. Both definitions are intentionally kept compatible. -/
inductive LatticeStep' : Type
  | east : LatticeStep'
  | north : LatticeStep'
  deriving DecidableEq, Repr

end LGV

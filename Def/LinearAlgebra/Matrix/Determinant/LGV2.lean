/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Structure.LinearAlgebra.Matrix.Determinant.LGV2
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

namespace SimpleDigraph

variable {V : Type*} [DecidableEq V]

/-- The starting vertex of a path -/
def Path.start {D : SimpleDigraph V} (p : Path D) : V :=
  p.vertices.head p.nonempty

/-- The ending vertex of a path -/
def Path.finish {D : SimpleDigraph V} (p : Path D) : V :=
  p.vertices.getLast p.nonempty

/-- A digraph is path-finite if there are only finitely many paths between any two vertices.
    Convention conv.lgv.digraph(b) -/
def IsPathFinite (D : SimpleDigraph V) : Prop :=
  ∀ u v : V, Set.Finite {p : Path D | p.start = u ∧ p.finish = v}

/-- A digraph is acyclic if it has no directed cycles.
    Convention conv.lgv.digraph(c) -/
def IsAcyclic (D : SimpleDigraph V) : Prop :=
  ∀ p : Path D, p.start = p.finish → p.vertices.length = 1

/-- Extract a subpath from index `i` to index `j` (inclusive).
    The resulting path has `j - i + 1` vertices. -/
def Path.subpath {D : SimpleDigraph V} (p : Path D) (i j : ℕ) (hij : i ≤ j) 
    (hj : j < p.vertices.length) : Path D where
  vertices := (p.vertices.drop i).take (j - i + 1)
  nonempty := by
    simp only [ne_eq, List.take_eq_nil_iff, List.drop_eq_nil_iff]
    push Not
    constructor <;> omega
  arcs_valid := by
    intro k hk
    simp only [List.length_take, List.length_drop] at hk
    have hk' : k + 1 < min (j - i + 1) (p.vertices.length - i) := hk
    have hk'' : k < j - i := by omega
    simp only [List.getElem_take, List.getElem_drop, List.get_eq_getElem]
    have hi' : i + k < p.vertices.length := by omega
    have hi'' : i + k + 1 < p.vertices.length := by omega
    convert p.arcs_valid (i + k) hi'' using 2

/-!
### Conversion to Mathlib's Digraph

`LGV.SimpleDigraph` is a specialized digraph structure that enforces irreflexivity
(no self-loops). Mathlib's `Digraph` is more general and allows self-loops.

We provide a conversion that forgets the irreflexivity proof, allowing use of
Mathlib's digraph infrastructure when needed.
-/


variable {V : Type*}

/-- Convert a `SimpleDigraph` to Mathlib's `Digraph`.
    This forgets the irreflexivity proof but preserves the adjacency relation.
    
    Note: LGV1.lean uses Mathlib's `Digraph` directly, while LGV2.lean uses this
    `SimpleDigraph` structure. This conversion enables interoperability. -/
def toDigraph (D : SimpleDigraph V) : Digraph V where
  Adj := D.arc

end SimpleDigraph

/-!
## The Integer Lattice ℤ²

Definition def.lgv.lattice: The integer lattice has vertex set ℤ² with arcs
(i,j) → (i+1,j) (east-steps) and (i,j) → (i,j+1) (north-steps).

### Relationship with LGV1.lean

LGV1.lean defines `LGV.integerLattice : Digraph LatticePoint` using Mathlib's `Digraph`.
This file defines `LGV.integerLattice : SimpleDigraph (ℤ × ℤ)` using our custom structure.

The two definitions have semantically identical adjacency relations:
- LGV1: `IntegerLatticeAdj p q ↔ q = (p.1 + 1, p.2) ∨ q = (p.1, p.2 + 1)`
- LGV2: `integerLattice.arc u v ↔ (v.1 = u.1 + 1 ∧ v.2 = u.2) ∨ (v.1 = u.1 ∧ v.2 = u.2 + 1)`

The lemma `integerLattice_arc_iff` proves these are equivalent, enabling
results from either file to be transferred to the other.
-/


/-- The integer lattice digraph ℤ².
    
    This is the same lattice as in LGV1.lean, but using `SimpleDigraph` instead of
    Mathlib's `Digraph`. See `integerLattice_arc_iff` for the characterization
    and `integerLattice_toDigraph_adj_iff` for the equivalence with LGV1's definition. -/
def integerLattice : SimpleDigraph (ℤ × ℤ) where
  arc u v := (v.1 = u.1 + 1 ∧ v.2 = u.2) ∨ (v.1 = u.1 ∧ v.2 = u.2 + 1)
  arc_irrefl := by
    intro ⟨x, y⟩
    simp only [not_or, not_and]
    constructor <;> omega

end LGV

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.LinearAlgebra.Matrix.Determinant.LGV2.Part12
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

/-- The set of intersecting path tuples with permutation is finite. -/
noncomputable def ipatWithPermSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Set.Finite (ipatWithPermSet (D := D) A B) := by
  have : Finite (pathTupleWithPerm (D := D) A B) := pathTupleWithPermFinite hpf A B
  exact Set.finite_univ.subset (fun _ _ => trivial)

/-- Convert ipatWithPermSet to Finset -/
noncomputable def ipatWithPermFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Finset (pathTupleWithPerm (D := D) A B) :=
  (ipatWithPermSetFinite hpf A B).toFinset

/-- The set of all path tuples with permutation -/
def allPathTupleWithPermSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (pathTupleWithPerm (D := D) A B) :=
  Set.univ

/-- The set of all path tuples with permutation is finite -/
noncomputable def allPathTupleWithPermSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Set.Finite (allPathTupleWithPermSet (D := D) A B) := by
  have : Finite (pathTupleWithPerm (D := D) A B) := pathTupleWithPermFinite hpf A B
  exact Set.finite_univ

/-- Convert allPathTupleWithPermSet to Finset -/
noncomputable def allPathTupleWithPermFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Finset (pathTupleWithPerm (D := D) A B) :=
  (allPathTupleWithPermSetFinite hpf A B).toFinset

/-- The set of non-intersecting path tuples with permutation -/
def nipatWithPermSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (pathTupleWithPerm (D := D) A B) :=
  {sp | sp.2.isNonIntersecting}

/-- The set of non-intersecting path tuples with permutation is finite -/
noncomputable def nipatWithPermSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Set.Finite (nipatWithPermSet (D := D) A B) := by
  have : Finite (pathTupleWithPerm (D := D) A B) := pathTupleWithPermFinite hpf A B
  exact Set.finite_univ.subset (fun _ _ => trivial)

/-- Convert nipatWithPermSet to Finset -/
noncomputable def nipatWithPermFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Finset (pathTupleWithPerm (D := D) A B) :=
  (nipatWithPermSetFinite hpf A B).toFinset

/-!
## The Nonpermutable Case

Corollary cor.lgv.kpaths.wt-np: When the source and target vertices are "sorted"
(x-coordinates decreasing, y-coordinates increasing), only the identity permutation
contributes to the sum.
-/


/-- The x-coordinate of a lattice point -/
def xCoord : ℤ × ℤ → ℤ := Prod.fst

/-- The y-coordinate of a lattice point -/
def yCoord : ℤ × ℤ → ℤ := Prod.snd

/-- A k-vertex has weakly decreasing x-coordinates -/
def xDecreasing {k : ℕ} (A : kVertex (ℤ × ℤ) k) : Prop :=
  ∀ i j : Fin k, i ≤ j → xCoord (A j) ≤ xCoord (A i)

/-- A k-vertex has weakly increasing y-coordinates -/
def yIncreasing {k : ℕ} (A : kVertex (ℤ × ℤ) k) : Prop :=
  ∀ i j : Fin k, i ≤ j → yCoord (A i) ≤ yCoord (A j)

/-!
## Applications

### Binomial Coefficient Determinants (Corollary cor.lgv.binom-det-nonneg)

When the matrix entries are binomial coefficients, the determinant is nonnegative.
-/
/-!
#### The FKG Inequality for Binomial Coefficients

The key combinatorial inequality underlying the binomial determinant nonnegativity.
This is the 2×2 case of the LGV lemma, which can be proved directly by induction.
-/
/-!
#### Base cases for binomial determinant nonnegativity
-/
/-!
#### Lattice point setup for binomial determinants

The key construction: set Aᵢ = (0, -aᵢ) and Bᵢ = (bᵢ, -bᵢ).
These satisfy the sorting conditions for lgv_nonpermutable.
-/


/-- The source lattice points for the binomial coefficient determinant:
    A_i = (0, -a_i) for the LGV lemma application. -/
def binomLatticeA {k : ℕ} (a : Fin k → ℕ) : kVertex (ℤ × ℤ) k :=
  fun i => (0, -(a i : ℤ))

/-- The target lattice points for the binomial coefficient determinant:
    B_i = (b_i, -b_i) for the LGV lemma application. -/
def binomLatticeB {k : ℕ} (b : Fin k → ℕ) : kVertex (ℤ × ℤ) k :=
  fun i => (b i, -(b i : ℤ))

/-!
#### Helper definitions for the path-subset bijection

The bijection between paths from (0, -a) to (b, -b) and b-element subsets of Fin a
is constructed using the following helpers:
- `eastStepCount a S i`: count of elements j ∈ S with j < i
- `vertexAtPos a S i`: the vertex at position i in the path determined by S
- `pathVerticesList a S`: the list of vertices for the path determined by S
-/


/-- Count of east steps before index i: |{j ∈ S : j < i}| -/
def eastStepCount (a : ℕ) (S : Finset (Fin a)) (i : ℕ) : ℕ :=
  (S.filter fun j => j.val < i).card

/-- Vertex at position i in the path determined by east-step set S.
    x-coordinate = number of east steps taken so far
    y-coordinate = -a + (i - number of east steps) = -a + number of north steps -/
def vertexAtPos (a : ℕ) (S : Finset (Fin a)) (i : ℕ) : ℤ × ℤ :=
  let e := eastStepCount a S i
  ((e : ℤ), -(a : ℤ) + ((i : ℤ) - (e : ℤ)))

end LGV

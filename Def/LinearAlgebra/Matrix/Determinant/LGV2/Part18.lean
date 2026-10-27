/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.LinearAlgebra.Matrix.Determinant.LGV2.Part16
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

/-- Bijection between paths from (0, -a) to (b, -b) and b-element subsets of Fin a.

    This encapsulates the key combinatorial bijection from Proposition prop.lgv.1-paths.ct:
    - A path from (0, -a) to (b, -b) has exactly a steps (coordinate sum goes from -a to 0)
    - A path has exactly b east-steps (x-coordinate goes from 0 to b)
    - A path is uniquely determined by which of its a steps are east-steps
    - This gives a bijection to b-element subsets of Fin a -/
noncomputable def paths_equiv_powersetCard (a b : ℕ) :
    (pathsFromTo integerLattice integerLattice_pathFinite (0, -(a : ℤ)) (b, -(b : ℤ))) ≃
      (Finset.powersetCard b (Finset.univ : Finset (Fin a))) := by
  -- The bijection: path ↔ set of east-step indices
  -- Forward: p ↦ {i : Fin a | step i is east}
  -- Backward: S ↦ path where step i is east iff i ∈ S
  refine ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
  case toFun =>
    intro ⟨p, hp⟩
    simp only [pathsFromTo, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hp
    have hstart := hp.1
    have hfinish := hp.2
    have hlen := path_length_from_endpoints a b p hstart hfinish
    have hcard := pathToEastSteps_card a b p hstart hfinish hlen
    exact ⟨pathToEastSteps a p hlen, by simp [Finset.mem_powersetCard, hcard]⟩
  case invFun =>
    intro ⟨S, hS⟩
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hS
    have hstart := eastStepsToPath_start a b S hS
    have hfinish := eastStepsToPath_finish a b S hS
    exact ⟨eastStepsToPath a b S hS, by simp [pathsFromTo, hstart, hfinish]⟩
  case left_inv =>
    intro ⟨p, hp⟩
    simp only [pathsFromTo, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hp
    have hstart := hp.1
    have hfinish := hp.2
    have hlen := path_length_from_endpoints a b p hstart hfinish
    have hcard := pathToEastSteps_card a b p hstart hfinish hlen
    simp only [Subtype.mk.injEq]
    -- Need to show: eastStepsToPath (pathToEastSteps p) = p
    have hvert := eastStepsToPath_pathToEastSteps_vertices a b p hstart hfinish hlen hcard
    -- Paths are equal iff their vertices are equal
    cases p
    simp only [eastStepsToPath] at hvert ⊢
    congr
  case right_inv =>
    intro ⟨S, hS⟩
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hS
    simp only [Subtype.mk.injEq]
    -- Need to show: pathToEastSteps (eastStepsToPath S) = S
    exact pathToEastSteps_eastStepsToPath a b S hS

/-!
#### Unit weight infrastructure for binomial determinant proof

The unit weight function assigns weight 1 to every arc. With this weight:
- pathWeight p = 1 for any path p
- pathTupleWeight ps = 1 for any path tuple ps
- pathWeightSum = cardinality of paths
- nipatWeightSum = cardinality of nipats ≥ 0
-/


/-- The unit arc weight function assigns 1 to every arc -/
noncomputable def unitArcWeight : ArcWeight integerLattice ℤ :=
  fun _ _ _ => 1

/-!
### Catalan Hankel Determinant (Corollary cor.lgv.catalan-hankel-det-0)

The Hankel determinant of Catalan numbers equals 1.

We use Mathlib's `catalan` function from `Mathlib.Combinatorics.Enumerative.Catalan`.
The Catalan numbers are defined by cₙ = C(2n,n)/(n+1), and the Hankel matrix
has entry (i,j) equal to c_{i+j}. This is a famous result that can be proven
using the LGV lemma with Dyck paths.
-/


/-- The Catalan Hankel matrix of size k×k, where entry (i,j) is c_{i+j}.
    Uses Mathlib's `catalan` function directly. -/
def catalanHankelMatrix (k : ℕ) : Matrix (Fin k) (Fin k) ℤ :=
  Matrix.of fun i j => (catalan ((i : ℕ) + (j : ℕ)) : ℤ)

/-- The explicit 7×7 Catalan Hankel matrix for native_decide.
    Using explicit matrix avoids timeout issues with `native_decide` on `catalanHankelMatrix 7`. -/
def catalanHankelMatrix7 : Matrix (Fin 7) (Fin 7) ℤ := 
  ![![1, 1, 2, 5, 14, 42, 132],
    ![1, 2, 5, 14, 42, 132, 429],
    ![2, 5, 14, 42, 132, 429, 1430],
    ![5, 14, 42, 132, 429, 1430, 4862],
    ![14, 42, 132, 429, 1430, 4862, 16796],
    ![42, 132, 429, 1430, 4862, 16796, 58786],
    ![132, 429, 1430, 4862, 16796, 58786, 208012]]

/-- The Dyck path digraph: vertices are ℤ × ℕ, arcs go (i,j) → (i+1, j+1) and (i,j) → (i+1, j-1).
    Used for counting Catalan numbers via Dyck paths.

    A Dyck path from (0,0) to (2n,0) corresponds to a balanced sequence of n up-steps
    and n down-steps that never goes below the x-axis. A Dyck path is a lattice path
    that stays on or above the x-axis, where each step goes either up-right or down-right. -/
def dyckDigraph : SimpleDigraph (ℤ × ℕ) where
  arc u v := (v.1 = u.1 + 1 ∧ v.2 = u.2 + 1) ∨
             (v.1 = u.1 + 1 ∧ v.2 + 1 = u.2 ∧ 0 < u.2)
  arc_irrefl := by
    intro ⟨x, y⟩
    simp only [not_or, not_and]
    constructor <;> omega

/-!
### Unit Arc Weight for Dyck Digraph

Infrastructure for connecting the Catalan Hankel matrix to the LGV lemma.
-/


/-- Unit arc weight for the Dyck digraph -/
noncomputable def dyckUnitArcWeight : ArcWeight dyckDigraph ℤ :=
  fun _ _ _ => 1

/-- Convert a Dyck path to a list of DyckSteps.
    Each arc (x,y) → (x+1,y+1) becomes U, each arc (x,y) → (x+1,y-1) becomes D. -/
def dyckPathToSteps (p : SimpleDigraph.Path dyckDigraph) : List DyckStep :=
  (List.finRange (p.vertices.length - 1)).map fun ⟨i, hi⟩ =>
    have hi' : i + 1 < p.vertices.length := by omega
    let u := p.vertices.get ⟨i, Nat.lt_of_succ_lt hi'⟩
    let v := p.vertices.get ⟨i + 1, hi'⟩
    if v.2 = u.2 + 1 then DyckStep.U else DyckStep.D

end LGV

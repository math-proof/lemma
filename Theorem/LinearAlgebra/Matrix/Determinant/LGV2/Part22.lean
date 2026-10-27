/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.LGV2.Part25
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

/-- The first vertex is the start point -/
theorem LatticePath'.toVertices_head (path : LatticePath') (start : ℤ × ℤ) :
    (LatticePath'.toVertices path start).head (LatticePath'.toVertices_nonempty path start) = start := by
  cases path <;> simp [toVertices]

/-- The start of the converted path is the original start point -/
theorem LatticePath'.toPath_start (path : LatticePath') (start : ℤ × ℤ) :
    (LatticePath'.toPath path start).start = start := by
  simp only [toPath, SimpleDigraph.Path.start, toVertices_head]

/-- The last vertex is the endpoint -/
theorem LatticePath'.toVertices_getLast (path : LatticePath') (start : ℤ × ℤ) :
    (LatticePath'.toVertices path start).getLast (LatticePath'.toVertices_nonempty path start) = 
    LatticePath'.endpoint path start := by
  induction path generalizing start with
  | nil => simp [toVertices, endpoint]
  | cons s rest ih =>
    simp only [toVertices, endpoint, List.foldl_cons]
    rw [List.getLast_cons (LatticePath'.toVertices_nonempty rest (s.apply start))]
    exact ih (s.apply start)

/-- The finish of the converted path is the endpoint -/
theorem LatticePath'.toPath_finish (path : LatticePath') (start : ℤ × ℤ) :
    (LatticePath'.toPath path start).finish = LatticePath'.endpoint path start := by
  simp only [toPath, SimpleDigraph.Path.finish, toVertices_getLast]

/-- The length of the vertex list equals the number of steps plus one -/
theorem LatticePath'.toVertices_length (path : LatticePath') (start : ℤ × ℤ) :
    (LatticePath'.toVertices path start).length = path.length + 1 := by
  induction path generalizing start with
  | nil => simp [toVertices]
  | cons s rest ih =>
    simp only [toVertices, List.length_cons]
    rw [ih (s.apply start)]

/-!
### Bridge Bijection Lemmas

The following lemmas establish that `LatticePath'.toPath` is a bijection between
step-based lattice paths and vertex-based digraph paths.

These lemmas provide the foundation for connecting LGV1.lean's counting results
with LGV2.lean's weighted results.
-/

/-- Two paths with the same vertices are equal -/
theorem SimpleDigraph.Path.ext_vertices' (p q : SimpleDigraph.Path integerLattice)
    (h : p.vertices = q.vertices) : p = q := by
  cases p; cases q
  simp only [SimpleDigraph.Path.mk.injEq]
  exact h

/-- toPath is injective: different step sequences give different paths.
    
    Proof sketch:
    1. If toPath p1 start = toPath p2 start, then their vertex lists are equal
    2. The vertex list uniquely determines the step sequence because:
       - Each arc in the integer lattice is uniquely determined by source and target
       - Given consecutive vertices u, v, the step is east iff v.1 = u.1 + 1
    3. By induction on the path length, equal vertex lists imply equal step sequences
    
    This is a key lemma for the bridge between LGV1 and LGV2 path representations. -/
theorem LatticePath'.toPath_injective (start : ℤ × ℤ) :
    Function.Injective (fun path => LatticePath'.toPath path start) := by
  intro p1 p2 h
  -- Two paths are equal iff their vertex lists are equal
  have hv : LatticePath'.toVertices p1 start = LatticePath'.toVertices p2 start := by
    have h1 : (LatticePath'.toPath p1 start).vertices = LatticePath'.toVertices p1 start := rfl
    have h2 : (LatticePath'.toPath p2 start).vertices = LatticePath'.toVertices p2 start := rfl
    rw [← h1, ← h2]
    exact congrArg SimpleDigraph.Path.vertices h
  -- Equal vertex lists imply equal step sequences
  -- The proof proceeds by induction on the path, showing that each step is uniquely
  -- determined by the pair of consecutive vertices in the integer lattice.
  -- Each step (east or north) produces a distinct target vertex from the same source.
  clear h
  induction p1 generalizing p2 start with
  | nil =>
    cases p2 with
    | nil => rfl
    | cons s rest =>
      exfalso
      have hlen1 : (toVertices [] start).length = 1 := by simp [toVertices]
      have hlen2 : (toVertices (s :: rest) start).length = (s :: rest).length + 1 := 
        toVertices_length (s :: rest) start
      rw [hv] at hlen1
      simp only [List.length_cons] at hlen2
      omega
  | cons s1 rest1 ih =>
    cases p2 with
    | nil =>
      exfalso
      have hlen1 : (toVertices [] start).length = 1 := by simp [toVertices]
      have hlen2 : (toVertices (s1 :: rest1) start).length = (s1 :: rest1).length + 1 := 
        toVertices_length (s1 :: rest1) start
      rw [← hv] at hlen1
      simp only [List.length_cons] at hlen2
      omega
    | cons s2 rest2 =>
      simp only [toVertices, List.cons.injEq] at hv
      -- Second vertices determine the steps
      have h_second : s1.apply start = s2.apply start := by
        have := hv.2
        cases rest1 <;> cases rest2 <;> simp only [toVertices, List.cons.injEq] at this
        all_goals first | exact this | exact this.1
      -- Since s1.apply start = s2.apply start, we have s1 = s2
      have h_step : s1 = s2 := by
        cases s1 <;> cases s2 <;> simp only [LatticeStep'.apply, Prod.mk.injEq] at h_second
        · rfl
        · omega
        · omega
        · rfl
      subst h_step
      congr 1
      -- Apply IH to the tails
      apply ih
      -- hv.2 is the equality of the tail vertex lists
      exact hv.2

end LGV

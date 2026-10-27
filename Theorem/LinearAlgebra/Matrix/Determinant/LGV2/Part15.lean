/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.LGV2.Part16
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

theorem eastStepsToPath_start (a b : ℕ) (S : Finset (Fin a)) (hcard : S.card = b) :
    (eastStepsToPath a b S hcard).start = (0, -(a : ℤ)) := by
  simp only [eastStepsToPath, SimpleDigraph.Path.start, List.head_eq_getElem]
  have h : 0 < a + 1 := Nat.zero_lt_succ a
  rw [pathVerticesList_getElem a S 0 h]
  exact vertexAtPos_zero a S

theorem eastStepsToPath_finish (a b : ℕ) (S : Finset (Fin a)) (hcard : S.card = b) :
    (eastStepsToPath a b S hcard).finish = ((b : ℤ), -(b : ℤ)) := by
  simp only [eastStepsToPath, SimpleDigraph.Path.finish]
  have hne : pathVerticesList a S ≠ [] := pathVerticesList_nonempty a S
  rw [List.getLast_eq_getElem]
  simp only [pathVerticesList, List.length_ofFn, List.getElem_ofFn]
  have h : a + 1 - 1 = a := by omega
  simp only [h, vertexAtPos, eastStepCount]
  have hfilter : S.filter (fun j => j.val < a) = S := by
    ext j; simp only [Finset.mem_filter, and_iff_left j.isLt]
  simp only [hfilter, hcard]
  ring_nf

/-- The length of eastStepsToPath is a + 1 -/
theorem eastStepsToPath_length (a b : ℕ) (S : Finset (Fin a)) (hcard : S.card = b) :
    (eastStepsToPath a b S hcard).vertices.length = a + 1 := by
  simp only [eastStepsToPath, pathVerticesList_length]

/-- For an arc in the integer lattice, the x-coordinate change is 0 or 1. -/
theorem integerLattice_arc_x_diff (u v : ℤ × ℤ) (h : integerLattice.arc u v) :
    v.1 - u.1 = 0 ∨ v.1 - u.1 = 1 := by
  rcases h with ⟨hx, _⟩ | ⟨hx, _⟩
  · right; omega
  · left; omega

/-- Telescoping sum: ∑ (f(i+1) - f(i)) = f(n) - f(0). -/
theorem sum_range_telescope' (n : ℕ) (f : ℕ → ℤ) :
    ∑ i ∈ Finset.range n, (f (i + 1) - f i) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ m ih => 
    rw [Finset.sum_range_succ, ih]
    ring

/-- When consecutive differences are 0 or 1, the count of 1s equals the total change. -/
theorem count_ones_eq_sum' (n b : ℕ) (f : ℕ → ℤ) 
    (hdiff : ∀ i < n, f (i + 1) - f i = 0 ∨ f (i + 1) - f i = 1)
    (hfirst : f 0 = 0) (hlast : f n = (b : ℤ)) :
    ((Finset.range n).filter (fun i => f (i + 1) = f i + 1)).card = b := by
  have h1 : ((Finset.range n).filter (fun i => f (i + 1) = f i + 1)).card = 
            ∑ i ∈ Finset.range n, if f (i + 1) = f i + 1 then 1 else 0 := by
    rw [Finset.card_filter]
  have h2 : ∀ i ∈ Finset.range n, (if f (i + 1) = f i + 1 then (1 : ℤ) else 0) = f (i + 1) - f i := by
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    rcases hdiff i hi' with h | h
    · have hne : f (i + 1) ≠ f i + 1 := by omega
      simp only [hne, ↓reduceIte, h]
    · have heq : f (i + 1) = f i + 1 := by omega
      simp only [heq, ↓reduceIte]; ring
  have h3 : (∑ i ∈ Finset.range n, if f (i + 1) = f i + 1 then (1 : ℤ) else 0) = 
            ∑ i ∈ Finset.range n, (f (i + 1) - f i) := by
    apply Finset.sum_congr rfl h2
  have h4 : (∑ i ∈ Finset.range n, (f (i + 1) - f i)) = (b : ℤ) := by
    rw [sum_range_telescope', hlast, hfirst]; ring
  have h5 : (∑ i ∈ Finset.range n, if f (i + 1) = f i + 1 then (1 : ℤ) else 0) = (b : ℤ) := h3.trans h4
  have h6 : (↑(∑ i ∈ Finset.range n, if f (i + 1) = f i + 1 then (1 : ℕ) else 0) : ℤ) = 
            ∑ i ∈ Finset.range n, if f (i + 1) = f i + 1 then (1 : ℤ) else 0 := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [h1]
  have h7 : (↑(∑ i ∈ Finset.range n, if f (i + 1) = f i + 1 then (1 : ℕ) else 0) : ℤ) = (b : ℤ) := by
    rw [h6, h5]
  exact Int.ofNat_inj.mp h7

end LGV

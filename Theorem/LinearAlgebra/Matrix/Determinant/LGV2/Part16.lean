/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.LGV2.Part17
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

/-- The east-step set has cardinality b for a path from (0, -a) to (b, -b) -/
theorem pathToEastSteps_card (a b : ℕ) (p : SimpleDigraph.Path integerLattice)
    (hstart : p.start = (0, -(a : ℤ))) (hfinish : p.finish = ((b : ℤ), -(b : ℤ)))
    (hlen : p.vertices.length = a + 1) :
    (pathToEastSteps a p hlen).card = b := by
  -- Define f(i) = x-coordinate of vertex i
  let f : ℕ → ℤ := fun i => 
    if h : i < p.vertices.length then (p.vertices.get ⟨i, h⟩).1 else 0
  -- Verify f(0) = 0
  have hf0 : f 0 = 0 := by
    simp only [f]
    have h0 : 0 < p.vertices.length := by rw [hlen]; omega
    simp only [h0, ↓reduceDIte]
    have heq : (p.vertices.get ⟨0, h0⟩).1 = p.start.1 := by
      simp [SimpleDigraph.Path.start, List.head_eq_getElem]
    rw [heq, hstart]
  -- Verify f(a) = b
  have hfa : f a = (b : ℤ) := by
    simp only [f]
    have ha : a < p.vertices.length := by rw [hlen]; omega
    simp only [ha, ↓reduceDIte]
    have h_last : p.vertices.get ⟨a, ha⟩ = p.finish := by
      simp only [SimpleDigraph.Path.finish, List.getLast_eq_getElem]
      congr 1
      simp only [hlen, Fin.ext_iff]
      omega
    rw [h_last, hfinish]
  -- Verify consecutive differences are 0 or 1
  have hdiff : ∀ i < a, f (i + 1) - f i = 0 ∨ f (i + 1) - f i = 1 := by
    intro i hi
    simp only [f]
    have hi1 : i + 1 < p.vertices.length := by rw [hlen]; omega
    have hi0 : i < p.vertices.length := Nat.lt_of_succ_lt hi1
    simp only [hi1, hi0, ↓reduceDIte]
    exact integerLattice_arc_x_diff _ _ (p.arcs_valid i hi1)
  -- Apply count_ones_eq_sum'
  have h := count_ones_eq_sum' a b f hdiff hf0 hfa
  -- Convert from Finset.range to Finset.univ (Fin a)
  have h_card_eq : (pathToEastSteps a p hlen).card = 
      ((Finset.range a).filter (fun i => f (i + 1) = f i + 1)).card := by
    simp only [pathToEastSteps]
    rw [Finset.card_filter, Finset.card_filter]
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < a := Finset.mem_range.mp hi
    simp only [f]
    have hi1 : i + 1 < p.vertices.length := by rw [hlen]; omega
    have hi0 : i < p.vertices.length := Nat.lt_of_succ_lt hi1
    simp only [hi1, hi0, ↓reduceDIte, hi', ↓reduceDIte]
  rw [h_card_eq, h]

/-- Round-trip: pathToEastSteps (eastStepsToPath S) = S -/
theorem pathToEastSteps_eastStepsToPath (a b : ℕ) (S : Finset (Fin a)) (hcard : S.card = b) :
    pathToEastSteps a (eastStepsToPath a b S hcard) (eastStepsToPath_length a b S hcard) = S := by
  ext i
  simp only [pathToEastSteps, Finset.mem_filter, Finset.mem_univ, true_and]
  -- We need to show: step i is east in eastStepsToPath iff i ∈ S
  -- The vertices of eastStepsToPath are given by vertexAtPos
  have hlen : (eastStepsToPath a b S hcard).vertices.length = a + 1 := eastStepsToPath_length a b S hcard
  have hi1 : i.val + 1 < (eastStepsToPath a b S hcard).vertices.length := by rw [hlen]; omega
  have hi0 : i.val < (eastStepsToPath a b S hcard).vertices.length := Nat.lt_of_succ_lt hi1
  -- Get the vertices
  have hget0 : (eastStepsToPath a b S hcard).vertices.get ⟨i.val, hi0⟩ = vertexAtPos a S i.val := by
    simp only [eastStepsToPath]
    have h1 : i.val < a + 1 := by omega
    have := pathVerticesList_getElem a S i.val h1
    convert this using 1
  have hget1 : (eastStepsToPath a b S hcard).vertices.get ⟨i.val + 1, hi1⟩ = vertexAtPos a S (i.val + 1) := by
    simp only [eastStepsToPath]
    have h2 : i.val + 1 < a + 1 := by rw [hlen] at hi1; exact hi1
    have := pathVerticesList_getElem a S (i.val + 1) h2
    convert this using 1
  rw [hget0, hget1]
  -- Now use the definition of vertexAtPos
  simp only [vertexAtPos, eastStepCount]
  constructor
  · -- If x increases, then i ∈ S
    intro hx
    -- x at i+1 minus x at i = 1 means i ∈ S
    have hfilter_i1 : (S.filter (fun j => j.val < i.val + 1)).card = 
                      (S.filter (fun j => j.val < i.val)).card + if i ∈ S then 1 else 0 := by
      by_cases hi : i ∈ S
      · simp only [hi, ↓reduceIte]
        have heq : S.filter (fun j => j.val < i.val + 1) = insert i (S.filter (fun j => j.val < i.val)) := by
          ext j; simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · intro ⟨hj, hlt⟩
            by_cases hji : j = i
            · left; exact hji
            · right; exact ⟨hj, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) (fun h => hji (Fin.ext h))⟩
          · intro h; rcases h with rfl | ⟨hj, hlt⟩
            · exact ⟨hi, Nat.lt_succ_self _⟩
            · exact ⟨hj, Nat.lt_succ_of_lt hlt⟩
        rw [heq]
        have hnotmem : i ∉ S.filter (fun j => j.val < i.val) := by
          simp only [Finset.mem_filter, not_and, not_lt]; intro _; exact le_refl _
        rw [Finset.card_insert_eq_ite, if_neg hnotmem]
      · simp only [hi, ↓reduceIte, add_zero]
        congr 1; ext j; simp only [Finset.mem_filter]
        constructor
        · intro ⟨hj, hlt⟩
          constructor
          · exact hj
          · by_cases hji : j.val = i.val
            · exfalso; have : j = i := Fin.ext hji; rw [this] at hj; exact hi hj
            · exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) hji
        · intro ⟨hj, hlt⟩; exact ⟨hj, Nat.lt_succ_of_lt hlt⟩
    -- From hx, we have that the x-coordinate increased by 1
    have hx' : (S.filter (fun j => j.val < i.val + 1)).card = 
               (S.filter (fun j => j.val < i.val)).card + 1 := by
      have := hx
      push_cast at this
      omega
    rw [hfilter_i1] at hx'
    by_cases hi : i ∈ S
    · exact hi
    · simp only [hi, ↓reduceIte, add_zero] at hx'; omega
  · -- If i ∈ S, then x increases
    intro hi
    have hfilter : (S.filter (fun j => j.val < i.val + 1)).card = 
                   (S.filter (fun j => j.val < i.val)).card + 1 := by
      have heq : S.filter (fun j => j.val < i.val + 1) = insert i (S.filter (fun j => j.val < i.val)) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · intro ⟨hj, hlt⟩
          by_cases hji : j = i
          · left; exact hji
          · right; exact ⟨hj, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) (fun h => hji (Fin.ext h))⟩
        · intro h; rcases h with rfl | ⟨hj, hlt⟩
          · exact ⟨hi, Nat.lt_succ_self _⟩
          · exact ⟨hj, Nat.lt_succ_of_lt hlt⟩
      rw [heq]
      have hnotmem : i ∉ S.filter (fun j => j.val < i.val) := by
        simp only [Finset.mem_filter, not_and, not_lt]; intro _; exact le_refl _
      rw [Finset.card_insert_eq_ite, if_neg hnotmem]
    simp only [hfilter]
    push_cast
    ring

/-- Path length for paths from (0, -a) to (b, -b) is a + 1 -/
theorem path_length_from_endpoints (a b : ℕ) (p : SimpleDigraph.Path integerLattice)
    (hstart : p.start = (0, -(a : ℤ))) (hfinish : p.finish = ((b : ℤ), -(b : ℤ))) :
    p.vertices.length = a + 1 := by
  have h := integerLattice_path_length_eq p
  rw [hstart, hfinish] at h
  omega

/-- The x-coordinate at position i equals the number of east steps before i -/
theorem path_x_coord_eq_eastSteps (a _b : ℕ) (p : SimpleDigraph.Path integerLattice)
    (hstart : p.start = (0, -(a : ℤ))) (hlen : p.vertices.length = a + 1) (i : ℕ) 
    (hi : i < p.vertices.length) :
    (p.vertices[i]).1 = ((pathToEastSteps a p hlen).filter (fun j => j.val < i)).card := by
  induction i with
  | zero =>
    have heq : p.vertices[0] = p.start := by
      simp [SimpleDigraph.Path.start, List.head_eq_getElem]
    rw [heq, hstart]
    have hempty : (pathToEastSteps a p hlen).filter (fun j => j.val < 0) = ∅ := by
      ext j
      simp only [Finset.mem_filter]
      constructor
      · intro ⟨_, hlt⟩; exact (Nat.not_lt_zero _ hlt).elim
      · simp
    simp only [hempty, Finset.card_empty, CharP.cast_eq_zero]
  | succ k ih =>
    have hk : k < p.vertices.length := Nat.lt_of_succ_lt hi
    specialize ih hk
    -- x at k+1 = x at k + (1 if step k is east, 0 otherwise)
    have harc := p.arcs_valid k hi
    rcases integerLattice_arc_x_diff _ _ harc with hstep | hstep
    · -- North step: x stays the same
      have hx_same : (p.vertices[k + 1]).1 = (p.vertices[k]).1 := by
        simp only [List.get_eq_getElem] at hstep; omega
      have hfilter_same : ((pathToEastSteps a p hlen).filter (fun j => j.val < k + 1)).card = 
                          ((pathToEastSteps a p hlen).filter (fun j => j.val < k)).card := by
        congr 1; ext j; simp only [Finset.mem_filter]
        have hkk : k < a := by omega
        constructor
        · intro ⟨hj, hlt⟩
          constructor
          · exact hj
          · by_cases hjk : j.val = k
            · -- j = k means step k is east, but we have north step
              exfalso
              simp only [pathToEastSteps, Finset.mem_filter, Finset.mem_univ, true_and] at hj
              have hj1 : j.val + 1 < p.vertices.length := by rw [hlen]; omega
              have hj' : (p.vertices[j.val + 1]).1 = (p.vertices[j.val]).1 + 1 := by
                convert hj using 2
              have hk1 : k + 1 < p.vertices.length := hi
              have : (p.vertices[k + 1]).1 = (p.vertices[k]).1 + 1 := by
                have hjk' : j.val = k := hjk
                simp only [hjk'] at hj'
                exact hj'
              omega
            · exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) hjk
        · intro ⟨hj, hlt⟩; exact ⟨hj, Nat.lt_succ_of_lt hlt⟩
      rw [hx_same, ih, hfilter_same]
    · -- East step: x increases by 1
      have hx_inc : (p.vertices[k + 1]).1 = (p.vertices[k]).1 + 1 := by
        simp only [List.get_eq_getElem] at hstep; omega
      have hkk : k < a := by omega
      have hk_in : (⟨k, hkk⟩ : Fin a) ∈ pathToEastSteps a p hlen := by
        simp only [pathToEastSteps, Finset.mem_filter, Finset.mem_univ, true_and]
        convert hx_inc using 2
      have hfilter_inc : ((pathToEastSteps a p hlen).filter (fun j => j.val < k + 1)).card = 
                         ((pathToEastSteps a p hlen).filter (fun j => j.val < k)).card + 1 := by
        have heq : (pathToEastSteps a p hlen).filter (fun j => j.val < k + 1) = 
                   insert ⟨k, hkk⟩ ((pathToEastSteps a p hlen).filter (fun j => j.val < k)) := by
          ext j; simp only [Finset.mem_filter, Finset.mem_insert, Fin.ext_iff]
          constructor
          · intro ⟨hj, hlt⟩
            by_cases hjk : j.val = k
            · left; exact hjk
            · right; exact ⟨hj, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) hjk⟩
          · intro h; rcases h with rfl | ⟨hj, hlt⟩
            · exact ⟨hk_in, Nat.lt_succ_self _⟩
            · exact ⟨hj, Nat.lt_succ_of_lt hlt⟩
        rw [heq]
        have hnotmem : (⟨k, hkk⟩ : Fin a) ∉ (pathToEastSteps a p hlen).filter (fun j => j.val < k) := by
          simp only [Finset.mem_filter, not_and, not_lt]; intro _; exact le_refl _
        rw [Finset.card_insert_eq_ite, if_neg hnotmem]
      rw [hx_inc, ih, hfilter_inc]
      push_cast; ring

/-- Round-trip: eastStepsToPath (pathToEastSteps p) produces a path with the same vertices -/
theorem eastStepsToPath_pathToEastSteps_vertices (a b : ℕ) (p : SimpleDigraph.Path integerLattice)
    (hstart : p.start = (0, -(a : ℤ))) (_hfinish : p.finish = ((b : ℤ), -(b : ℤ)))
    (hlen : p.vertices.length = a + 1) (hcard : (pathToEastSteps a p hlen).card = b) :
    (eastStepsToPath a b (pathToEastSteps a p hlen) hcard).vertices = p.vertices := by
  -- Both paths have the same length
  have hlen' : (eastStepsToPath a b (pathToEastSteps a p hlen) hcard).vertices.length = a + 1 := 
    eastStepsToPath_length a b (pathToEastSteps a p hlen) hcard
  -- Show vertices are equal by showing each vertex is equal
  apply List.ext_getElem
  · rw [hlen', hlen]
  · intro i hi1 hi2
    -- hi1 : i < (eastStepsToPath ...).vertices.length
    -- hi2 : i < p.vertices.length
    have hi1' : i < a + 1 := by rw [hlen'] at hi1; exact hi1
    -- Get the i-th vertex of eastStepsToPath
    have hget_east : (eastStepsToPath a b (pathToEastSteps a p hlen) hcard).vertices[i] = 
                     vertexAtPos a (pathToEastSteps a p hlen) i := by
      simp only [eastStepsToPath]
      have := pathVerticesList_getElem a (pathToEastSteps a p hlen) i hi1'
      convert this using 1
    rw [hget_east]
    -- Show vertexAtPos matches p.vertices[i]
    simp only [vertexAtPos, eastStepCount]
    -- Use the extracted lemma for x-coordinate
    have hx := path_x_coord_eq_eastSteps a b p hstart hlen i hi2
    have hy : (p.vertices[i]).2 = 
              -(a : ℤ) + ((i : ℤ) - ((pathToEastSteps a p hlen).filter (fun j => j.val < i)).card) := by
      have hsum := integerLattice_path_vertex_sum p i hi2
      rw [hstart] at hsum
      simp only [List.get_eq_getElem] at hsum
      omega
    ext
    · exact hx.symm
    · exact hy.symm

end LGV

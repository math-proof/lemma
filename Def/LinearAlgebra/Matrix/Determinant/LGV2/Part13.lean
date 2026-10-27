/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.LinearAlgebra.Matrix.Determinant.LGV2.Part11
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

noncomputable def getCanonicalIntersectionData {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    { data : (i : Fin k) × (j : Fin k) × { v : V // v ∈ (pt.paths i).vertices ∧ v ∈ (pt.paths j).vertices } // 
      data.1 ≠ data.2.1 } :=
  let hne := pt.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip
  let i := pt.crowdedPathIndices.min' hne
  let hi : i ∈ pt.crowdedPathIndices := Finset.min'_mem _ hne
  let idx := pt.firstCrowdedIndexOnPath i
  let h_idx := pt.firstCrowdedIndexOnPath_lt_length i hi
  let v := (pt.paths i).vertices.get ⟨idx, h_idx⟩
  let hv_crowded := pt.firstCrowdedVertex_mem_crowdedVerticesOnPath i hi
    let hv_i : v ∈ (pt.paths i).vertices := by
      simp only [PathTuple.crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hv_crowded
      exact hv_crowded.1
    let h_sdiff_ne := pt.pathIndicesContaining_sdiff_singleton_nonempty i hi v hv_crowded
    let j := (pt.pathIndicesContaining v \ {i}).max' h_sdiff_ne
    let hj_mem : j ∈ pt.pathIndicesContaining v \ {i} := Finset.max'_mem _ h_sdiff_ne
    let hj_ne_i : j ≠ i := by
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj_mem
      exact hj_mem.2
    let hv_j : v ∈ (pt.paths j).vertices := by
      simp only [Finset.mem_sdiff, Finset.mem_singleton, PathTuple.pathIndicesContaining, 
                 Finset.mem_filter, Finset.mem_univ, true_and] at hj_mem
      exact hj_mem.1
  ⟨⟨i, j, ⟨v, hv_i, hv_j⟩⟩, hj_ne_i.symm⟩


/-- The sign-reversing involution on intersecting path tuples.
    For an ipat (σ, 𝐩), we:
    1. Find the smallest i such that p_i contains a crowded point
    2. Find the first crowded point v on p_i
    3. Find the largest j such that v is on p_j
    4. Exchange tails of p_i and p_j at v
    5. Compose σ with the transposition t_{i,j}
    This gives (σ ∘ t_{i,j}, 𝐩') which is still an ipat.

    **Implementation note:** The permutation component is `sp.1 * Equiv.swap i j` where
    i and j are the intersection indices. The path tuple component uses `exchangeTails`
    to swap the tails of paths i and j at the crowded vertex v. -/
noncomputable def signReversing {D : SimpleDigraph V} (_hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) : pathTupleWithPerm (D := D) A B :=
  let ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩ := getCanonicalIntersectionData sp.2 hip
  let newPaths : Fin k → SimpleDigraph.Path D := fun l =>
    if h : l = i then (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1
    else if h' : l = j then (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).2
    else sp.2.paths l
  have h_starts : ∀ l, (newPaths l).start = A l := by
    intro l
    simp only [newPaths]
    split_ifs with h h'
    · rw [h, exchangeTails_fst_start, sp.2.starts]
    · rw [h', exchangeTails_snd_start, sp.2.starts]
    · exact sp.2.starts l
  have h_finishes : ∀ l, (newPaths l).finish = (permuteKVertex (sp.1 * Equiv.swap i j) B) l := by
    intro l
    simp only [newPaths, permuteKVertex, Equiv.Perm.coe_mul, Function.comp_apply]
    split_ifs with h h'
    · -- l = i case
      rw [h, exchangeTails_fst_finish, sp.2.finishes]
      simp only [permuteKVertex, Equiv.swap_apply_left]
    · -- l = j case  
      rw [h', exchangeTails_snd_finish, sp.2.finishes]
      simp only [permuteKVertex, Equiv.swap_apply_right]
    · -- l ≠ i, l ≠ j case
      rw [sp.2.finishes]
      simp only [permuteKVertex]
      congr 1
      rw [Equiv.swap_apply_of_ne_of_ne h h']
    ⟨sp.1 * Equiv.swap i j, ⟨newPaths, h_starts, h_finishes⟩⟩

/-!
## Infrastructure for LGV Proof

The following definitions and lemmas provide the infrastructure needed to complete
the LGV theorem proof. The key steps are:
1. Define the finset of all path tuples
2. Define the finset of intersecting path tuples (ipats)
3. Prove that the signed sum over ipats is 0 using the sign-reversing involution
-/


/-- The set of all path tuples from A to B -/
def allPathTupleSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (PathTuple D k A B) :=
  Set.univ

/-- The set of all path tuples is finite (follows from path-finiteness) -/
noncomputable def allPathTupleSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Set.Finite (allPathTupleSet (D := D) A B) := by
  -- The proof is essentially the same as nipatSetFinite
  let pathSets : Fin k → Set (SimpleDigraph.Path D) := fun i => 
    {p : SimpleDigraph.Path D | p.start = A i ∧ p.finish = B i}
  have h_each_finite : ∀ i, Set.Finite (pathSets i) := fun i => hpf (A i) (B i)
  have h_prod_finite : Set.Finite (Set.pi Set.univ pathSets) := 
    Set.Finite.pi (fun i => h_each_finite i)
  let f : (allPathTupleSet (D := D) A B) → Set.pi Set.univ pathSets := fun ⟨pt, _⟩ =>
    ⟨pt.paths, fun i _ => ⟨pt.starts i, pt.finishes i⟩⟩
  have hf_inj : Function.Injective f := by
    intro ⟨pt1, _⟩ ⟨pt2, _⟩ heq
    simp only [Subtype.mk.injEq, f] at heq ⊢
    cases pt1; cases pt2
    simp only [PathTuple.mk.injEq] at heq ⊢
    exact congrArg Subtype.val heq
  have h_pi_finite : Finite (Set.pi Set.univ pathSets) := h_prod_finite
  have h_finite : Finite (allPathTupleSet (D := D) A B) := Finite.of_injective f hf_inj
  exact Set.finite_coe_iff.mp h_finite

/-- Convert allPathTupleSet to Finset -/
noncomputable def allPathTupleFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : Finset (PathTuple D k A B) :=
  (allPathTupleSetFinite hpf A B).toFinset

/-- The set of intersecting path tuples (ipats) -/
def ipatSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (PathTuple D k A B) :=
  {pt | pt.isIntersecting}

/-- The set of ipats is finite -/
noncomputable def ipatSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : Set.Finite (ipatSet (D := D) A B) :=
  (allPathTupleSetFinite hpf A B).subset (fun _ _ => trivial)

/-- Convert ipatSet to Finset -/
noncomputable def ipatFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : Finset (PathTuple D k A B) :=
  (ipatSetFinite hpf A B).toFinset

/-- The set of all intersecting path tuples with permutation.
    This is the domain of the sign-reversing involution. -/
def ipatWithPermSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (pathTupleWithPerm (D := D) A B) :=
  {sp | sp.2.isIntersecting}

end LGV

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.LinearAlgebra.Matrix.Determinant.LGV2.Part2
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

/-- Two paths have a vertex in common -/
def pathsIntersect {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) : Prop :=
  ∃ v, v ∈ p.vertices ∧ v ∈ q.vertices

/-- A path tuple is non-intersecting (nipat) if no two paths share a vertex.
    Definition def.lgv.path-tups(d) -/
def PathTuple.isNonIntersecting {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) : Prop :=
  ∀ i j, i ≠ j → ¬pathsIntersect (pt.paths i) (pt.paths j)

/-- A path tuple is intersecting (ipat) if some two paths share a vertex.
    Definition def.lgv.path-tups(e) -/
def PathTuple.isIntersecting {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) : Prop :=
  ¬pt.isNonIntersecting

/-!
## The Path Weight Matrix

The matrix M where M_{i,j} = ∑_{p : Aᵢ → Bⱼ} w(p).
-/


/-- The set of paths from u to v in a path-finite digraph -/
noncomputable def pathsFromTo {V : Type*} [DecidableEq V] (D : SimpleDigraph V)
    (hpf : D.IsPathFinite) (u v : V) : Finset (SimpleDigraph.Path D) :=
  (hpf u v).toFinset

/-- The sum of weights of all paths from u to v.
    ∑_{p : u → v} w(p) -/
noncomputable def pathWeightSum {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) (w : ArcWeight D K) (u v : V) : K :=
  ∑ p ∈ pathsFromTo D hpf u v, pathWeight w p

/-- The path weight matrix M_{i,j} = ∑_{p : Aᵢ → Bⱼ} w(p) -/
noncomputable def pathWeightMatrix {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) (w : ArcWeight D K) {k : ℕ}
    (A B : kVertex V k) : Matrix (Fin k) (Fin k) K :=
  Matrix.of fun i j => pathWeightSum hpf w (A i) (B j)

/-!
## LGV Lemma: Weighted Lattice Version

Theorem thm.lgv.kpaths.wt: For the integer lattice with arc weights w,
det(M) = ∑_{σ ∈ Sₖ} (-1)^σ ∑_{𝐩 nipat from 𝐀 to σ(𝐁)} w(𝐩)
-/


/-- The set of non-intersecting path tuples from 𝐀 to 𝐁 -/
noncomputable def nipatSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (PathTuple D k A B) :=
  {pt | pt.isNonIntersecting}

/-- The set of nipats is finite (follows from path-finiteness) -/
noncomputable def nipatSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : Set.Finite (nipatSet (D := D) A B) := by
  -- The set of all path tuples from A to B is finite
  have h_all_finite : Set.Finite {pt : PathTuple D k A B | True} := by
    let pathSets : Fin k → Set (SimpleDigraph.Path D) := fun i => 
      {p : SimpleDigraph.Path D | p.start = A i ∧ p.finish = B i}
    have h_each_finite : ∀ i, Set.Finite (pathSets i) := fun i => hpf (A i) (B i)
    have h_prod_finite : Set.Finite (Set.pi Set.univ pathSets) := 
      Set.Finite.pi (fun i => h_each_finite i)
    -- Define the map from PathTuple to the pi type
    let f : {pt : PathTuple D k A B | True} → Set.pi Set.univ pathSets := fun ⟨pt, _⟩ =>
      ⟨pt.paths, fun i _ => ⟨pt.starts i, pt.finishes i⟩⟩
    have hf_inj : Function.Injective f := by
      intro ⟨pt1, _⟩ ⟨pt2, _⟩ heq
      simp only [Subtype.mk.injEq, f] at heq ⊢
      cases pt1; cases pt2
      simp only [PathTuple.mk.injEq] at heq ⊢
      exact congrArg Subtype.val heq
    -- The pi type is finite
    have h_pi_finite : Finite (Set.pi Set.univ pathSets) := h_prod_finite
    -- Since f is injective and the codomain is finite, the domain is finite
    have h_finite : Finite {pt : PathTuple D k A B | True} := Finite.of_injective f hf_inj
    exact Set.finite_coe_iff.mp h_finite
  exact h_all_finite.subset (fun _ _ => trivial)

/-- Convert nipatSet to Finset using the finiteness proof -/
noncomputable def nipatFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : Finset (PathTuple D k A B) :=
  (nipatSetFinite hpf A B).toFinset

/-- Sum of weights over all nipats from 𝐀 to 𝐁
    Note: σ is not used in this definition since the permutation is already
    encoded in B (which should be permuteKVertex σ B' for some B') -/
noncomputable def nipatWeightSum {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) (w : ArcWeight D K) {k : ℕ}
    (A B : kVertex V k) (_σ : Equiv.Perm (Fin k)) : K :=
  ∑ pt ∈ nipatFinset hpf A B, pathTupleWeight w pt.paths

/-!
## Path Tuple Infrastructure for LGV

The key step in the LGV proof is to express the product of sums as a sum over path tuples:
  ∏_j (∑_{p : A_j → B_j} w(p)) = ∑_{pt : PathTuple} pathTupleWeight w pt.paths

This uses `Finset.prod_univ_sum` and a bijection between PathTuple and the piFinset.
-/


/-- Bijection between PathTuple and the piFinset of pathsFromTo.
    This is the key to converting the product of sums to a sum over path tuples. -/
noncomputable def pathTupleEquivPiFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) :
    PathTuple D k A B ≃ (Fintype.piFinset (fun j => pathsFromTo D hpf (A j) (B j))) := by
  refine ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
  case toFun =>
    intro pt
    refine ⟨pt.paths, ?_⟩
    simp only [Fintype.mem_piFinset, pathsFromTo, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    intro j
    exact ⟨pt.starts j, pt.finishes j⟩
  case invFun =>
    intro ⟨f, hf⟩
    simp only [Fintype.mem_piFinset, pathsFromTo, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hf
    exact ⟨f, fun j => (hf j).1, fun j => (hf j).2⟩
  case left_inv =>
    intro pt
    rfl
  case right_inv =>
    intro ⟨f, hf⟩
    rfl

/-!
## LGV Lemma: General Digraph Version

Theorem thm.lgv.kpaths.wt-dg: The same result holds for any path-finite acyclic digraph.

The proof uses a sign-reversing involution on intersecting path tuples. The key steps are:

1. Express det(M) using the Leibniz formula as ∑_σ (-1)^σ ∏_i M_{i,σ(i)}
2. Expand each product as a sum over path tuples from 𝐀 to σ(𝐁)
3. Define a sign-reversing involution f on intersecting path tuples:
   - Find the first crowded point (vertex in multiple paths)
   - Pick the smallest index i whose path contains a crowded point
   - Pick the first crowded point v on path p_i
   - Pick the largest index j such that v is on path p_j
   - Exchange the tails of p_i and p_j at v
   - This maps (σ, 𝐩) to (σ ∘ t_{i,j}, 𝐩'), where t_{i,j} is the transposition
4. The involution preserves weight but flips sign, so intersecting tuples cancel
5. Only non-intersecting path tuples (nipats) contribute to the sum
-/


variable {V : Type*} [DecidableEq V]

/-- A crowded point in a path tuple is a vertex that appears in at least two paths -/
def PathTuple.isCrowded {D : SimpleDigraph V} {k : ℕ} {A B : kVertex V k}
    (pt : PathTuple D k A B) (v : V) : Prop :=
  ∃ i j : Fin k, i ≠ j ∧ v ∈ (pt.paths i).vertices ∧ v ∈ (pt.paths j).vertices

end LGV

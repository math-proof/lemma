/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
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


open Finset BigOperators Matrix

namespace LGV
/-!
## Digraph Definitions

We work with simple digraphs that are path-finite and acyclic.
-/


/-- A simple digraph with vertex set V.
    Convention conv.lgv.digraph(d): A simple digraph has arcs as pairs of distinct vertices. -/
structure SimpleDigraph (V : Type*) where
  /-- The arc relation: `arc u v` means there is an arc from `u` to `v` -/
  arc : V → V → Prop
  /-- No self-loops -/
  arc_irrefl : ∀ v, ¬arc v v

namespace SimpleDigraph

variable {V : Type*} [DecidableEq V]

/-- A path in a digraph is a list of vertices where consecutive vertices are connected by arcs.
    A path may contain 0 arcs (in which case start and end are identical). -/
structure Path (D : SimpleDigraph V) where
  /-- The vertices of the path, in order -/
  vertices : List V
  /-- The path is nonempty -/
  nonempty : vertices ≠ []
  /-- Consecutive vertices are connected by arcs -/
  arcs_valid : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length, D.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
      (vertices.get ⟨i + 1, hi⟩)

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

/-- Each arc in the integer lattice increases coordinates (or keeps them equal) -/
theorem integerLattice_arc_nondecreasing (u v : ℤ × ℤ) (h : integerLattice.arc u v) :
    u.1 ≤ v.1 ∧ u.2 ≤ v.2 := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega

/-- Each arc in the integer lattice increases the sum x + y by exactly 1 -/
theorem integerLattice_arc_sum (u v : ℤ × ℤ) (h : integerLattice.arc u v) :
    v.1 + v.2 = u.1 + u.2 + 1 := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega

/-- Coordinates are monotone along a path in the integer lattice -/
theorem integerLattice_path_monotone (p : SimpleDigraph.Path integerLattice) (i j : ℕ)
    (hi : i < p.vertices.length) (hj : j < p.vertices.length) (hij : i ≤ j) :
    (p.vertices.get ⟨i, hi⟩).1 ≤ (p.vertices.get ⟨j, hj⟩).1 ∧
    (p.vertices.get ⟨i, hi⟩).2 ≤ (p.vertices.get ⟨j, hj⟩).2 := by
  induction j with
  | zero =>
    simp only [Nat.le_zero] at hij
    subst hij
    constructor <;> rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hik
    · constructor <;> rfl
    · have hk : k < p.vertices.length := Nat.lt_of_succ_lt hj
      have hik' : i ≤ k := Nat.lt_succ_iff.mp hik
      obtain ⟨h1, h2⟩ := ih hk hik'
      have harc : integerLattice.arc (p.vertices.get ⟨k, hk⟩) (p.vertices.get ⟨k + 1, hj⟩) :=
        p.arcs_valid k hj
      obtain ⟨h3, h4⟩ := integerLattice_arc_nondecreasing _ _ harc
      exact ⟨le_trans h1 h3, le_trans h2 h4⟩

/-- Start coordinates ≤ finish coordinates for any path in the integer lattice -/
theorem integerLattice_path_start_le_finish (p : SimpleDigraph.Path integerLattice) :
    p.start.1 ≤ p.finish.1 ∧ p.start.2 ≤ p.finish.2 := by
  have hne := p.nonempty
  have hlen : 0 < p.vertices.length := List.length_pos_of_ne_nil hne
  have hlast : p.vertices.length - 1 < p.vertices.length := Nat.sub_lt hlen Nat.one_pos
  have h := integerLattice_path_monotone p 0 (p.vertices.length - 1) hlen hlast (Nat.zero_le _)
  simp only [SimpleDigraph.Path.start, SimpleDigraph.Path.finish]
  convert h using 2 <;> simp [List.head_eq_getElem, List.getLast_eq_getElem]

/-- Helper for path_sum_eq: proves the sum formula by induction on the list -/
theorem integerLattice_path_sum_eq_aux (l : List (ℤ × ℤ)) (hne : l ≠ [])
    (harcs : ∀ i : ℕ, ∀ hi : i + 1 < l.length, integerLattice.arc (l.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (l.get ⟨i + 1, hi⟩)) :
    (l.getLast hne).1 + (l.getLast hne).2 = (l.head hne).1 + (l.head hne).2 + (l.length - 1) := by
  induction l with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      have hne' : y :: ys ≠ [] := List.cons_ne_nil y ys
      have harcs' : ∀ i : ℕ, ∀ hi : i + 1 < (y :: ys).length,
          integerLattice.arc ((y :: ys).get ⟨i, Nat.lt_of_succ_lt hi⟩) ((y :: ys).get ⟨i + 1, hi⟩) := by
        intro i hi
        have hi' : (i + 1) + 1 < (x :: y :: ys).length := by simp at hi ⊢; omega
        have := harcs (i + 1) hi'
        simp only [List.length_cons, List.get_cons_succ] at this ⊢
        exact this
      have harc_xy : integerLattice.arc x y := by
        have := harcs 0 (by simp : 0 + 1 < (x :: y :: ys).length)
        simp at this
        exact this
      have hsum_xy := integerLattice_arc_sum x y harc_xy
      specialize ih hne' harcs'
      simp only [List.getLast_cons hne', List.head_cons, List.length_cons] at ih ⊢
      omega

/-- The sum of coordinates increases by exactly (length - 1) along a path -/
theorem integerLattice_path_sum_eq (p : SimpleDigraph.Path integerLattice) :
    p.finish.1 + p.finish.2 = p.start.1 + p.start.2 + (p.vertices.length - 1) :=
  integerLattice_path_sum_eq_aux p.vertices p.nonempty p.arcs_valid

/-- Path length is determined by start and finish coordinates -/
theorem integerLattice_path_length_eq (p : SimpleDigraph.Path integerLattice) :
    (p.vertices.length : ℤ) = p.finish.1 + p.finish.2 - p.start.1 - p.start.2 + 1 := by
  have h := integerLattice_path_sum_eq p
  have hpos : 0 < p.vertices.length := List.length_pos_of_ne_nil p.nonempty
  omega

/-- Sum at vertex i equals start sum + i -/
theorem integerLattice_path_vertex_sum (p : SimpleDigraph.Path integerLattice) (i : ℕ)
    (hi : i < p.vertices.length) :
    (p.vertices.get ⟨i, hi⟩).1 + (p.vertices.get ⟨i, hi⟩).2 = p.start.1 + p.start.2 + i := by
  induction i with
  | zero =>
    simp only [SimpleDigraph.Path.start, CharP.cast_eq_zero, add_zero]
    have : p.vertices.get ⟨0, hi⟩ = p.vertices.head p.nonempty := by
      simp [List.head_eq_getElem, List.get_eq_getElem]
    rw [this]
  | succ k ih =>
    have hk : k < p.vertices.length := Nat.lt_of_succ_lt hi
    have ihk := ih hk
    have harc := p.arcs_valid k hi
    have hsum := integerLattice_arc_sum _ _ harc
    omega

/-- Vertices of a lattice path are bounded by start and finish coordinates -/
theorem integerLattice_path_vertices_bounded (p : SimpleDigraph.Path integerLattice) (i : ℕ)
    (hi : i < p.vertices.length) :
    p.start.1 ≤ (p.vertices.get ⟨i, hi⟩).1 ∧ (p.vertices.get ⟨i, hi⟩).1 ≤ p.finish.1 ∧
    p.start.2 ≤ (p.vertices.get ⟨i, hi⟩).2 ∧ (p.vertices.get ⟨i, hi⟩).2 ≤ p.finish.2 := by
  have hne := p.nonempty
  have hlen : 0 < p.vertices.length := List.length_pos_of_ne_nil hne
  have hlast : p.vertices.length - 1 < p.vertices.length := Nat.sub_lt hlen Nat.one_pos
  have h1 := integerLattice_path_monotone p 0 i hlen hi (Nat.zero_le _)
  have h2 := integerLattice_path_monotone p i (p.vertices.length - 1) hi hlast (Nat.le_sub_one_of_lt hi)
  simp only [SimpleDigraph.Path.start, SimpleDigraph.Path.finish]
  constructor
  · convert h1.1 using 1; simp [List.head_eq_getElem]
  constructor
  · convert h2.1 using 1; simp [List.getLast_eq_getElem]
  constructor
  · convert h1.2 using 1; simp [List.head_eq_getElem]
  · convert h2.2 using 1; simp [List.getLast_eq_getElem]

/-- Paths in the integer lattice are determined by their vertex list -/
theorem integerLattice_path_ext (p q : SimpleDigraph.Path integerLattice)
    (h : p.vertices = q.vertices) : p = q := by
  cases p; cases q
  simp only [SimpleDigraph.Path.mk.injEq] at h ⊢
  exact h

/-- The integer lattice is path-finite -/
theorem integerLattice_pathFinite : integerLattice.IsPathFinite := by
  intro u v
  by_cases h : v.1 < u.1 ∨ v.2 < u.2
  · -- Case 1: No paths exist (would need to go backwards)
    convert Set.finite_empty
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hstart hfinish
    have hle := integerLattice_path_start_le_finish p
    rw [hstart, hfinish] at hle
    omega
  · -- Case 2: Paths exist but are finite
    push Not at h
    -- Define the path length and bounding box
    let n := (v.1 - u.1 + v.2 - u.2 + 1).toNat
    let box : Finset (ℤ × ℤ) := (Finset.Icc u.1 v.1) ×ˢ (Finset.Icc u.2 v.2)
    -- Define the subtype of paths from u to v
    let S := {p : SimpleDigraph.Path integerLattice | p.start = u ∧ p.finish = v}
    -- Show S is finite by injecting into Fin n → box
    suffices Finite S by exact Set.finite_coe_iff.mpr this
    -- Define the injection: map each path to its vertex list as a function
    let f : S → (Fin n → box) := fun ⟨p, hp⟩ i =>
      let hi : i.val < p.vertices.length := by
        have hlen := integerLattice_path_length_eq p
        rw [hp.1, hp.2] at hlen
        simp only [n] at hlen ⊢
        have := i.isLt
        omega
      ⟨p.vertices.get ⟨i.val, hi⟩, by
        have hbd := integerLattice_path_vertices_bounded p i.val hi
        rw [hp.1, hp.2] at hbd
        simp only [box, Finset.mem_product, Finset.mem_Icc]
        exact ⟨⟨hbd.1, hbd.2.1⟩, ⟨hbd.2.2.1, hbd.2.2.2⟩⟩⟩
    have hinj : Function.Injective f := by
      intro ⟨p, hp⟩ ⟨q, hq⟩ heq
      simp only [Subtype.mk.injEq, f] at heq ⊢
      apply integerLattice_path_ext
      apply List.ext_get
      · -- Lengths are equal (both determined by u and v)
        have hlenp := integerLattice_path_length_eq p
        have hlenq := integerLattice_path_length_eq q
        rw [hp.1, hp.2] at hlenp
        rw [hq.1, hq.2] at hlenq
        omega
      · -- Elements are equal at each position
        intro i hip hiq
        have heqi := congr_fun heq ⟨i, by
          have hlenp := integerLattice_path_length_eq p
          rw [hp.1, hp.2] at hlenp
          simp only [n]
          omega⟩
        simp only [Subtype.mk.injEq] at heqi
        exact heqi
    exact Finite.of_injective f hinj
/-!
## Path Weights

For each arc, we assign a weight from a commutative ring K.
The weight of a path is the product of its arc weights.
-/


variable {V : Type*} [DecidableEq V] {K : Type*} [CommRing K]

/-- An arc weight function assigns a ring element to each arc.
    Definition in Theorem thm.lgv.kpaths.wt -/
def ArcWeight (D : SimpleDigraph V) (K : Type*) := (u v : V) → D.arc u v → K

/-- Helper function to compute the product of arc weights along a vertex list.
    Uses recursion on the structure of the list.
    - For an empty list or single vertex, the weight is 1 (no arcs).
    - For a list [v₀, v₁, ...], the weight is w(v₀, v₁) * (weight of [v₁, ...]). -/
noncomputable def pathWeightAux {D : SimpleDigraph V} (w : ArcWeight D K)
    (vertices : List V) (arcs_valid : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      D.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩)) : K :=
  match vertices with
  | [] => 1
  | [_] => 1
  | v₀ :: v₁ :: rest =>
    have h : 0 + 1 < (v₀ :: v₁ :: rest).length := by simp
    have arc_proof : D.arc v₀ v₁ := by
      have := arcs_valid 0 h
      simp at this
      exact this
    have rest_arcs_valid : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
        D.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩) ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
      intro i hi
      have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
      have := arcs_valid (i + 1) hi'
      simp only [List.length_cons, List.get_cons_succ] at this ⊢
      exact this
    w v₀ v₁ arc_proof * pathWeightAux w (v₁ :: rest) rest_arcs_valid

/-- The weight of a path is the product of weights of its arcs.
    w(p) := ∏_{a is an arc of p} w(a) -/
noncomputable def pathWeight {D : SimpleDigraph V} (w : ArcWeight D K) (p : SimpleDigraph.Path D) : K :=
  pathWeightAux w p.vertices p.arcs_valid

/-- The weight of a path tuple is the product of weights of its component paths.
    w(𝐩) := w(p₁) w(p₂) ⋯ w(pₖ) -/
noncomputable def pathTupleWeight {D : SimpleDigraph V} {k : ℕ} (w : ArcWeight D K)
    (ps : Fin k → SimpleDigraph.Path D) : K :=
  ∏ i, pathWeight w (ps i)
/-!
## k-Vertices and Path Tuples

Definition def.lgv.path-tups: A k-vertex is a k-tuple of vertices.
A path tuple from 𝐀 to 𝐁 is a k-tuple of paths where pᵢ goes from Aᵢ to Bᵢ.
-/


/-- A k-vertex is a k-tuple of vertices of D.
    Definition def.lgv.path-tups(a) -/
abbrev kVertex (V : Type*) (k : ℕ) := Fin k → V

/-- Permute a k-vertex by a permutation σ: σ(𝐀) = (A_{σ(1)}, A_{σ(2)}, ..., A_{σ(k)}).
    Definition def.lgv.path-tups(b) -/
def permuteKVertex {V : Type*} {k : ℕ} (σ : Equiv.Perm (Fin k)) (A : kVertex V k) : kVertex V k :=
  fun i => A (σ i)

/-- A path tuple from 𝐀 to 𝐁 is a k-tuple (p₁, ..., pₖ) where pᵢ is a path from Aᵢ to Bᵢ.
    Definition def.lgv.path-tups(c) -/
structure PathTuple {V : Type*} [DecidableEq V] (D : SimpleDigraph V) (k : ℕ)
    (A B : kVertex V k) where
  /-- The paths in the tuple -/
  paths : Fin k → SimpleDigraph.Path D
  /-- Each path starts at the corresponding source vertex -/
  starts : ∀ i, (paths i).start = A i
  /-- Each path ends at the corresponding target vertex -/
  finishes : ∀ i, (paths i).finish = B i

@[ext]
theorem PathTuple.ext {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt1 pt2 : PathTuple D k A B)
    (h : ∀ i, pt1.paths i = pt2.paths i) : pt1 = pt2 := by
  cases pt1; cases pt2
  simp only [PathTuple.mk.injEq]
  ext i
  exact h i

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

/-- An intersecting path tuple has at least one crowded point -/
theorem PathTuple.isIntersecting_iff_exists_crowded {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) :
    pt.isIntersecting ↔ ∃ v, pt.isCrowded v := by
  unfold isIntersecting isNonIntersecting isCrowded pathsIntersect
  push Not
  constructor
  · intro ⟨i, j, hij, v, hvi, hvj⟩
    exact ⟨v, i, j, hij, hvi, hvj⟩
  · intro ⟨v, i, j, hij, hvi, hvj⟩
    exact ⟨i, j, hij, v, hvi, hvj⟩

/-- The set of path tuples from 𝐀 to σ(𝐁) paired with the permutation σ -/
abbrev pathTupleWithPerm {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Type _ :=
  (σ : Equiv.Perm (Fin k)) × PathTuple D k A (permuteKVertex σ B)

/-- The sign of a path tuple with permutation is (-1)^σ -/
def signOfPathTupleWithPerm {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (sp : pathTupleWithPerm (D := D) A B) : ℤˣ :=
  Equiv.Perm.sign sp.1

/-- The weight of a path tuple with permutation -/
noncomputable def weightOfPathTupleWithPerm {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (w : ArcWeight D K) (sp : pathTupleWithPerm (D := D) A B) : K :=
  pathTupleWeight w sp.2.paths

/-- The index of the first occurrence of a vertex in a path's vertex list -/
def firstIndexIn {D : SimpleDigraph V} (p : SimpleDigraph.Path D) (v : V) : ℕ :=
  p.vertices.findIdx (· = v)

/-- Split a path at a vertex v, returning (head ending at v, tail starting at v).
    The head includes v, the tail starts at v. -/
noncomputable def SimpleDigraph.Path.splitAt {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : SimpleDigraph.Path D × SimpleDigraph.Path D :=
  let idx := p.vertices.findIdx (· = v)
  let head := p.vertices.take (idx + 1)
  let tail := p.vertices.drop idx
  have h_idx_lt : idx < p.vertices.length := 
    List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_head_ne : head ≠ [] := by
    intro h
    have hlen : head.length = 0 := by simp [h]
    simp only [head, List.length_take] at hlen
    omega
  have h_tail_ne : tail ≠ [] := by
    intro h
    have hlen : tail.length = 0 := by rw [h]; rfl
    simp only [tail, List.length_drop] at hlen
    omega
  have h_head_arcs : ∀ i : ℕ, ∀ hi : i + 1 < head.length,
      D.arc (head.get ⟨i, Nat.lt_of_succ_lt hi⟩) (head.get ⟨i + 1, hi⟩) := by
    intro i hi
    simp only [head, List.length_take, lt_min_iff] at hi
    have hi2 : i + 1 < p.vertices.length := by omega
    have := p.arcs_valid i hi2
    simp only [List.get_eq_getElem] at this ⊢
    simp only [head]
    rw [List.getElem_take, List.getElem_take]
    exact this
  have h_tail_arcs : ∀ i : ℕ, ∀ hi : i + 1 < tail.length,
      D.arc (tail.get ⟨i, Nat.lt_of_succ_lt hi⟩) (tail.get ⟨i + 1, hi⟩) := by
    intro i hi
    simp only [tail, List.length_drop] at hi
    have hi2 : idx + i + 1 < p.vertices.length := by omega
    have := p.arcs_valid (idx + i) hi2
    simp only [List.get_eq_getElem] at this ⊢
    simp only [tail]
    rw [List.getElem_drop, List.getElem_drop]
    convert this using 2
  (⟨head, h_head_ne, h_head_arcs⟩, ⟨tail, h_tail_ne, h_tail_arcs⟩)

/-- The head of splitAt ends at v -/
theorem SimpleDigraph.Path.splitAt_head_finish {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : (p.splitAt v hv).1.finish = v := by
  unfold splitAt SimpleDigraph.Path.finish
  simp only
  have h_idx_lt : p.vertices.findIdx (· = v) < p.vertices.length := 
    List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_len : (p.vertices.take (p.vertices.findIdx (· = v) + 1)).length = 
               p.vertices.findIdx (· = v) + 1 := by
    rw [List.length_take]
    omega
  have h_ne : p.vertices.take (p.vertices.findIdx (· = v) + 1) ≠ [] := by
    intro h
    have : (p.vertices.take (p.vertices.findIdx (· = v) + 1)).length = 0 := by simp [h]
    omega
  rw [List.getLast_eq_getElem]
  have h_idx : (p.vertices.take (p.vertices.findIdx (· = v) + 1)).length - 1 = 
               p.vertices.findIdx (· = v) := by
    rw [h_len]; omega
  simp only [h_idx, List.getElem_take]
  have := @List.findIdx_getElem V (· = v) p.vertices h_idx_lt
  simp at this
  exact this

/-- The tail of splitAt starts at v -/
theorem SimpleDigraph.Path.splitAt_tail_start {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : (p.splitAt v hv).2.start = v := by
  unfold splitAt SimpleDigraph.Path.start
  simp only
  have h_idx_lt : p.vertices.findIdx (· = v) < p.vertices.length := 
    List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_ne : p.vertices.drop (p.vertices.findIdx (· = v)) ≠ [] := by
    intro h
    have hlen : (p.vertices.drop (p.vertices.findIdx (· = v))).length = 0 := by rw [h]; rfl
    simp only [List.length_drop] at hlen
    omega
  rw [List.head_eq_getElem]
  simp only [List.getElem_drop, Nat.add_zero]
  have := @List.findIdx_getElem V (· = v) p.vertices h_idx_lt
  simp at this
  exact this

/-- Concatenate two paths where the first path ends at v and the second starts at v.
    The resulting path goes from the start of the first to the end of the second.
    The vertex v appears once in the result (not duplicated). -/
noncomputable def SimpleDigraph.Path.concat {D : SimpleDigraph V} (p q : SimpleDigraph.Path D) 
    (hpq : p.finish = q.start) : SimpleDigraph.Path D :=
  let vertices := p.vertices ++ q.vertices.tail
  have h_ne : vertices ≠ [] := by
    simp only [vertices]
    intro h
    have hlen : (p.vertices ++ q.vertices.tail).length = 0 := by rw [h]; rfl
    simp only [List.length_append, List.length_tail] at hlen
    have hp_ne := p.nonempty
    have hp_len : p.vertices.length ≠ 0 := by
      intro h
      exact hp_ne (List.eq_nil_of_length_eq_zero h)
    omega
  have h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      D.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩) := by
    intro i hi
    simp only [vertices, List.length_append, List.length_tail] at hi
    simp only [List.get_eq_getElem, vertices]
    by_cases h : i + 1 < p.vertices.length
    · rw [List.getElem_append_left (by omega), List.getElem_append_left h]
      exact p.arcs_valid i h
    · push Not at h
      by_cases h' : i < p.vertices.length
      · have hi_eq : i = p.vertices.length - 1 := by omega
        have hq_len : 1 < q.vertices.length := by
          have hq_ne := q.nonempty
          by_contra hq_short
          push Not at hq_short
          have htail_len : q.vertices.tail.length = 0 := by simp only [List.length_tail]; omega
          omega
        rw [List.getElem_append_left h', List.getElem_append_right (by omega)]
        have h1 : p.vertices[i]'h' = p.finish := by 
          simp only [SimpleDigraph.Path.finish, hi_eq, List.getLast_eq_getElem]
        have h_idx : i + 1 - p.vertices.length = 0 := by omega
        have h2 : q.vertices.tail[i + 1 - p.vertices.length]'(by simp; omega) = q.vertices[1]'hq_len := by
          simp only [h_idx, List.getElem_tail]
        rw [h1, h2, hpq]
        have hq_arc := q.arcs_valid 0 hq_len
        simp only [List.get_eq_getElem, SimpleDigraph.Path.start, List.head_eq_getElem] at hq_arc ⊢
        exact hq_arc
      · push Not at h'
        have hi1 : i - p.vertices.length < q.vertices.tail.length := by simp; omega
        have hi2 : i + 1 - p.vertices.length < q.vertices.tail.length := by simp; omega
        rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
        have h1 : q.vertices.tail[i - p.vertices.length]'hi1 = 
                  q.vertices[i - p.vertices.length + 1]'(by simp at hi1; omega) := by 
          simp only [List.getElem_tail]
        have h2 : q.vertices.tail[i + 1 - p.vertices.length]'hi2 = 
                  q.vertices[i + 1 - p.vertices.length + 1]'(by simp at hi2; omega) := by 
          simp only [List.getElem_tail]
        rw [h1, h2]
        have hq_arc := q.arcs_valid (i - p.vertices.length + 1) (by simp at hi2; omega)
        simp only [List.get_eq_getElem] at hq_arc
        convert hq_arc using 2; omega
  ⟨vertices, h_ne, h_arcs⟩

omit [DecidableEq V] in
/-- The concatenation of two paths starts at the first path's start -/
theorem SimpleDigraph.Path.concat_start {D : SimpleDigraph V} (p q : SimpleDigraph.Path D) 
    (hpq : p.finish = q.start) : (p.concat q hpq).start = p.start := by
  unfold concat start
  simp only
  exact List.head_append_of_ne_nil (l' := q.vertices.tail) p.nonempty

omit [DecidableEq V] in
/-- The concatenation of two paths ends at the second path's finish -/
theorem SimpleDigraph.Path.concat_finish {D : SimpleDigraph V} (p q : SimpleDigraph.Path D) 
    (hpq : p.finish = q.start) : (p.concat q hpq).finish = q.finish := by
  unfold concat finish
  simp only
  have hq_ne := q.nonempty
  by_cases h : q.vertices.tail = []
  · have hq_len : q.vertices.length = 1 := by
      have : q.vertices.tail.length = 0 := by simp [h]
      simp only [List.length_tail] at this
      have hq_pos : 0 < q.vertices.length := List.length_pos_of_ne_nil hq_ne
      omega
    have hq_finish_eq_start : q.vertices.getLast hq_ne = q.vertices.head hq_ne := by
      rw [List.getLast_eq_getElem, List.head_eq_getElem]; congr; omega
    simp only [h, List.append_nil]
    rw [hq_finish_eq_start]
    unfold start at hpq
    rw [← hpq]; unfold finish; rfl
  · rw [List.getLast_append_of_ne_nil _ h, List.getLast_tail h]

/-- The head of splitAt starts at the original path's start -/
theorem SimpleDigraph.Path.splitAt_head_start {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : (p.splitAt v hv).1.start = p.start := by
  unfold splitAt start
  simp only
  have h_idx_lt : p.vertices.findIdx (· = v) < p.vertices.length := 
    List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_head_ne : p.vertices.take (p.vertices.findIdx (· = v) + 1) ≠ [] := by
    intro h; have hlen : (p.vertices.take (p.vertices.findIdx (· = v) + 1)).length = 0 := by simp [h]
    simp only [List.length_take] at hlen; omega
  exact List.head_take h_head_ne

/-- The tail of splitAt ends at the original path's finish -/
theorem SimpleDigraph.Path.splitAt_tail_finish {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : (p.splitAt v hv).2.finish = p.finish := by
  unfold splitAt finish
  simp only
  have h_idx_lt : p.vertices.findIdx (· = v) < p.vertices.length := 
    List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_drop_ne : p.vertices.drop (p.vertices.findIdx (· = v)) ≠ [] := by
    intro h; have hlen : (p.vertices.drop (p.vertices.findIdx (· = v))).length = 0 := by rw [h]; rfl
    simp only [List.length_drop] at hlen; omega
  rw [List.getLast_drop h_drop_ne]

/-- Exchange the tails of two paths at a common vertex.
    If p goes A → v → B and q goes A' → v → B', then after exchange:
    p' goes A → v → B' and q' goes A' → v → B -/
noncomputable def exchangeTails {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    SimpleDigraph.Path D × SimpleDigraph.Path D :=
  let sp_p := p.splitAt v hv_p
  let sp_q := q.splitAt v hv_q
  let head_p := sp_p.1
  let tail_p := sp_p.2
  let head_q := sp_q.1
  let tail_q := sp_q.2
  have h1 : head_p.finish = tail_q.start := by
    have hp := SimpleDigraph.Path.splitAt_head_finish p v hv_p
    have hq := SimpleDigraph.Path.splitAt_tail_start q v hv_q
    simp only [head_p, sp_p, tail_q, sp_q] at *
    rw [hp, hq]
  have h2 : head_q.finish = tail_p.start := by
    have hp := SimpleDigraph.Path.splitAt_tail_start p v hv_p
    have hq := SimpleDigraph.Path.splitAt_head_finish q v hv_q
    simp only [tail_p, sp_p, head_q, sp_q] at *
    rw [hq, hp]
  (SimpleDigraph.Path.concat head_p tail_q h1, SimpleDigraph.Path.concat head_q tail_p h2)

/-- The first path from exchangeTails starts at the original first path's start -/
theorem exchangeTails_fst_start {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    (exchangeTails p q v hv_p hv_q).1.start = p.start := by
  unfold exchangeTails
  simp only
  rw [SimpleDigraph.Path.concat_start]
  exact SimpleDigraph.Path.splitAt_head_start p v hv_p

/-- The first path from exchangeTails ends at the original second path's finish -/
theorem exchangeTails_fst_finish {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    (exchangeTails p q v hv_p hv_q).1.finish = q.finish := by
  unfold exchangeTails
  simp only
  rw [SimpleDigraph.Path.concat_finish]
  exact SimpleDigraph.Path.splitAt_tail_finish q v hv_q

/-- The second path from exchangeTails starts at the original second path's start -/
theorem exchangeTails_snd_start {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    (exchangeTails p q v hv_p hv_q).2.start = q.start := by
  unfold exchangeTails
  simp only
  rw [SimpleDigraph.Path.concat_start]
  exact SimpleDigraph.Path.splitAt_head_start q v hv_q

/-- The second path from exchangeTails ends at the original first path's finish -/
theorem exchangeTails_snd_finish {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    (exchangeTails p q v hv_p hv_q).2.finish = p.finish := by
  unfold exchangeTails
  simp only
  rw [SimpleDigraph.Path.concat_finish]
  exact SimpleDigraph.Path.splitAt_tail_finish p v hv_p
/-!
### Deterministic Intersection Data Selection

The sign-reversing involution requires selecting intersection data (i, j, v) deterministically
so that applying the involution twice returns the original path tuple. The algorithm from
the LaTeX source is:
1. Pick the smallest i such that path i contains a crowded point
2. Pick the first crowded point v on path i (by position in the path)
3. Pick the largest j such that v is on path j

This selection is preserved under the involution because:
- The heads of paths i and j (before v) are unchanged
- So v is still the first crowded point on path i
- And j is still the largest index containing v
-/


/-- The set of path indices that have a crowded vertex (shared with another path) -/
def PathTuple.crowdedPathIndices {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) : Finset (Fin k) :=
  Finset.univ.filter fun i =>
    ∃ j : Fin k, i ≠ j ∧ ((pt.paths i).vertices.toFinset ∩ (pt.paths j).vertices.toFinset).Nonempty

/-- The set of crowded vertices on a specific path -/
def PathTuple.crowdedVerticesOnPath {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (i : Fin k) : Finset V :=
  (pt.paths i).vertices.toFinset.filter fun v =>
    ∃ j : Fin k, i ≠ j ∧ v ∈ (pt.paths j).vertices

/-- The set of path indices that contain a given vertex -/
def PathTuple.pathIndicesContaining {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (v : V) : Finset (Fin k) :=
  Finset.univ.filter fun i => v ∈ (pt.paths i).vertices

/-- The index of the first crowded vertex on a path (by position) -/
def PathTuple.firstCrowdedIndexOnPath {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (i : Fin k) : ℕ :=
  (pt.paths i).vertices.findIdx fun v => v ∈ pt.crowdedVerticesOnPath i

/-- An intersecting path tuple has nonempty crowdedPathIndices -/
theorem PathTuple.isIntersecting_iff_crowdedPathIndices_nonempty {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) :
    pt.isIntersecting ↔ pt.crowdedPathIndices.Nonempty := by
  rw [PathTuple.isIntersecting_iff_exists_crowded]
  constructor
  · intro ⟨v, i, j, hij, hvi, hvj⟩
    use i
    simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    use j, hij, v
    simp only [Finset.mem_inter, List.mem_toFinset]
    exact ⟨hvi, hvj⟩
  · intro ⟨i, hi⟩
    simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨j, hij, v, hv⟩ := hi
    simp only [Finset.mem_inter, List.mem_toFinset] at hv
    exact ⟨v, i, j, hij, hv.1, hv.2⟩

/-!
### Canonical Intersection Data Selection

The sign-reversing involution requires selecting intersection data (i, j, v) canonically
so that applying the involution twice returns the original path tuple. The algorithm is:
1. i = the smallest path index that contains a crowded point
2. v = the first crowded point on path i (by position in the vertex list)
3. j = the largest path index that contains v

This selection is preserved under the involution because:
- The heads of paths i and j (before v) are unchanged by exchangeTails
- So v is still the first crowded point on path i
- And j is still the largest index containing v
-/


/-- Get the smallest crowded path index. -/
def PathTuple.minCrowdedPathIndex {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) : Fin k :=
  pt.crowdedPathIndices.min' (pt.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip)

/-- The minimum crowded path index is in crowdedPathIndices -/
theorem PathTuple.minCrowdedPathIndex_mem {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    pt.minCrowdedPathIndex hip ∈ pt.crowdedPathIndices :=
  Finset.min'_mem _ _

/-- The crowded vertices on the minimum path are nonempty -/
theorem PathTuple.crowdedVerticesOnPath_minCrowded_nonempty {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    (pt.crowdedVerticesOnPath (pt.minCrowdedPathIndex hip)).Nonempty := by
  have hi_mem := pt.minCrowdedPathIndex_mem hip
  simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi_mem
  obtain ⟨j, hij, v, hv⟩ := hi_mem
  simp only [Finset.mem_inter, List.mem_toFinset] at hv
  use v
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset]
  exact ⟨hv.1, j, hij, hv.2⟩
noncomputable def PathTuple.firstCrowdedVertex {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) : V :=
  let i := pt.minCrowdedPathIndex hip
  let crowded := pt.crowdedVerticesOnPath i
  -- Find the first vertex in the path that is crowded
  ((pt.paths i).vertices.find? (fun v => v ∈ crowded)).get (by
    -- Prove that find? returns some
    have hne := pt.crowdedVerticesOnPath_minCrowded_nonempty hip
    obtain ⟨v, hv⟩ := hne
    apply List.find?_isSome.mpr
    use v
    constructor
    · -- v is in the path
      simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hv
      exact hv.1
    · -- v ∈ crowded
      simp only [decide_eq_true_eq]
      exact hv)

/-- The first crowded vertex is in the crowdedVerticesOnPath set -/
theorem PathTuple.firstCrowdedVertex_mem_crowded {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    pt.firstCrowdedVertex hip ∈ pt.crowdedVerticesOnPath (pt.minCrowdedPathIndex hip) := by
  unfold firstCrowdedVertex
  have hne := pt.crowdedVerticesOnPath_minCrowded_nonempty hip
  obtain ⟨v, hv⟩ := hne
  have h_isSome : ((pt.paths (pt.minCrowdedPathIndex hip)).vertices.find? 
      (fun v => v ∈ pt.crowdedVerticesOnPath (pt.minCrowdedPathIndex hip))).isSome := by
    apply List.find?_isSome.mpr
    use v
    constructor
    · simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hv
      exact hv.1
    · simp only [decide_eq_true_eq]
      exact hv
  have h := Option.get_mem h_isSome
  have hprop := List.find?_some h
  simp only [decide_eq_true_eq] at hprop
  exact hprop

/-- The first crowded vertex is crowded (shared with another path) -/
theorem PathTuple.firstCrowdedVertex_is_crowded {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    ∃ j : Fin k, pt.minCrowdedPathIndex hip ≠ j ∧ 
      pt.firstCrowdedVertex hip ∈ (pt.paths j).vertices := by
  have hcrowded := pt.firstCrowdedVertex_mem_crowded hip
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hcrowded
  exact hcrowded.2
noncomputable def PathTuple.otherPathsContainingFirstCrowded {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) : Finset (Fin k) :=
  (pt.pathIndicesContaining (pt.firstCrowdedVertex hip)).filter 
    (fun j => j ≠ pt.minCrowdedPathIndex hip)

/-- The set of other paths containing the first crowded vertex is nonempty -/
theorem PathTuple.otherPathsContainingFirstCrowded_nonempty {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    (pt.otherPathsContainingFirstCrowded hip).Nonempty := by
  obtain ⟨j, hij, hvj⟩ := pt.firstCrowdedVertex_is_crowded hip
  use j
  simp only [otherPathsContainingFirstCrowded, Finset.mem_filter, pathIndicesContaining,
    Finset.mem_univ, true_and]
  exact ⟨hvj, hij.symm⟩
noncomputable def PathTuple.maxOtherPathIndex {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) : Fin k :=
  (pt.otherPathsContainingFirstCrowded hip).max' (pt.otherPathsContainingFirstCrowded_nonempty hip)

/-- Helper function to extract intersection indices from an intersecting path tuple.
    Returns a pair (i, j) with i ≠ j such that paths i and j intersect. -/
noncomputable def getIntersectionIndices {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    { p : Fin k × Fin k // p.1 ≠ p.2 } :=
  Classical.choice (by
    -- Convert isIntersecting to existential form using isIntersecting_iff_exists_crowded
    rw [PathTuple.isIntersecting_iff_exists_crowded] at hip
    obtain ⟨v, i, j, hij, _, _⟩ := hip
    exact ⟨⟨(i, j), hij⟩⟩)

/-- Helper function to extract full intersection data from an intersecting path tuple.
    Returns (i, j, v, hvi, hvj) where i ≠ j and v is on both paths i and j. -/
noncomputable def getIntersectionData {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    { data : (i : Fin k) × (j : Fin k) × { v : V // v ∈ (pt.paths i).vertices ∧ v ∈ (pt.paths j).vertices } // 
      data.1 ≠ data.2.1 } :=
  Classical.choice (by
    rw [PathTuple.isIntersecting_iff_exists_crowded] at hip
    obtain ⟨v, i, j, hij, hvi, hvj⟩ := hip
    exact ⟨⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩⟩)
/-!
### Canonical (Deterministic) Intersection Data Selection

To prove that signReversing is an involution, we need to select intersection data
(i, j, v) deterministically so that the same selection is made before and after
applying the involution.

The canonical selection algorithm:
1. i = smallest index in crowdedPathIndices (using Finset.min')
2. v = first crowded vertex on path i (by position in the path)
3. j = largest index in pathIndicesContaining v, excluding i (using Finset.max')

This selection is preserved under exchangeTails because:
- The head of path i (vertices before v) is unchanged
- So v is still the first crowded vertex on path i
- And j is still the largest index containing v
-/

/-- A crowded path index has at least 2 paths containing some crowded vertex -/
theorem PathTuple.crowdedPathIndex_pathIndicesContaining_card {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices)
    (v : V) (hv : v ∈ pt.crowdedVerticesOnPath i) :
    1 < (pt.pathIndicesContaining v).card := by
  simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hv
  obtain ⟨hvi, j, hij, hvj⟩ := hv
  have hi_mem : i ∈ pt.pathIndicesContaining v := by
    simp only [pathIndicesContaining, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hvi
  have hj_mem : j ∈ pt.pathIndicesContaining v := by
    simp only [pathIndicesContaining, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hvj
  have hne : i ≠ j := hij
  calc (pt.pathIndicesContaining v).card 
      ≥ ({i, j} : Finset (Fin k)).card := Finset.card_le_card (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hi_mem
        · exact hj_mem)
    _ = 2 := by simp [hne]
    _ > 1 := by omega

/-- If i is a crowded path index, the set of other path indices containing a crowded vertex on i
    is nonempty -/
theorem PathTuple.pathIndicesContaining_sdiff_singleton_nonempty {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices)
    (v : V) (hv : v ∈ pt.crowdedVerticesOnPath i) :
    (pt.pathIndicesContaining v \ {i}).Nonempty := by
  have hcard := pt.crowdedPathIndex_pathIndicesContaining_card i hi v hv
  rw [Finset.sdiff_nonempty]
  intro h
  have hsub : pt.pathIndicesContaining v ⊆ {i} := h
  have : (pt.pathIndicesContaining v).card ≤ ({i} : Finset (Fin k)).card := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at this
  omega

/-- A crowded path index has nonempty crowdedVerticesOnPath -/
theorem PathTuple.crowdedPathIndex_crowdedVerticesOnPath_nonempty {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices) :
    (pt.crowdedVerticesOnPath i).Nonempty := by
  simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨j, hij, v, hv⟩ := hi
  simp only [Finset.mem_inter, List.mem_toFinset] at hv
  use v
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset]
  exact ⟨hv.1, j, hij, hv.2⟩

/-- The first crowded vertex on path i (when i is a crowded path index) exists in the path -/
theorem PathTuple.firstCrowdedIndexOnPath_lt_length {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices) :
    pt.firstCrowdedIndexOnPath i < (pt.paths i).vertices.length := by
  have hne := pt.crowdedPathIndex_crowdedVerticesOnPath_nonempty i hi
  obtain ⟨v, hv⟩ := hne
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hv
  unfold firstCrowdedIndexOnPath
  apply List.findIdx_lt_length_of_exists
  use v, hv.1
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset, decide_eq_true_eq]
  exact hv

/-- The vertex at firstCrowdedIndexOnPath is in crowdedVerticesOnPath -/
theorem PathTuple.firstCrowdedVertex_mem_crowdedVerticesOnPath {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices) :
    let idx := pt.firstCrowdedIndexOnPath i
    let h := pt.firstCrowdedIndexOnPath_lt_length i hi
    (pt.paths i).vertices.get ⟨idx, h⟩ ∈ pt.crowdedVerticesOnPath i := by
  simp only
  unfold firstCrowdedIndexOnPath
  have h_lt := pt.firstCrowdedIndexOnPath_lt_length i hi
  unfold firstCrowdedIndexOnPath at h_lt
  have h_findIdx := @List.findIdx_getElem _ (fun v => v ∈ pt.crowdedVerticesOnPath i) 
    (pt.paths i).vertices h_lt
  simp only [List.get_eq_getElem]
  simp at h_findIdx
  exact h_findIdx
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

/-- PathTuple is finite when the digraph is path-finite. -/
theorem pathTupleFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Finite (PathTuple D k A B) := by
  have h := allPathTupleSetFinite hpf A B
  -- allPathTupleSet A B = Set.univ, so h : Set.Finite Set.univ
  -- We need to convert this to Finite (PathTuple D k A B)
  rw [allPathTupleSet] at h
  exact Set.finite_univ_iff.mp h

/-- pathTupleWithPerm is finite when the digraph is path-finite. -/
theorem pathTupleWithPermFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Finite (pathTupleWithPerm (D := D) A B) := by
  unfold pathTupleWithPerm
  have h_perm_finite : Finite (Equiv.Perm (Fin k)) := inferInstance
  have h_pt_finite : ∀ σ : Equiv.Perm (Fin k), 
      Finite (PathTuple D k A (permuteKVertex σ B)) := by
    intro σ
    exact pathTupleFinite hpf A (permuteKVertex σ B)
  exact inferInstance

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

/-- vertexAtPos 0 = (0, -a) -/
theorem vertexAtPos_zero (a : ℕ) (S : Finset (Fin a)) : 
    vertexAtPos a S 0 = (0, -(a : ℤ)) := by
  simp only [vertexAtPos, eastStepCount]
  have h : S.filter (fun j => j.val < 0) = ∅ := by
    ext j; simp only [Finset.mem_filter]
    constructor
    · intro ⟨_, hlt⟩; exact (Nat.not_lt_zero _ hlt).elim
    · simp
  simp only [h, Finset.card_empty, CharP.cast_eq_zero, sub_zero, add_zero]

/-- The list of vertices for the path determined by S -/
def pathVerticesList (a : ℕ) (S : Finset (Fin a)) : List (ℤ × ℤ) :=
  List.ofFn (fun i : Fin (a + 1) => vertexAtPos a S i.val)

theorem pathVerticesList_length (a : ℕ) (S : Finset (Fin a)) :
    (pathVerticesList a S).length = a + 1 := by simp [pathVerticesList]

theorem pathVerticesList_nonempty (a : ℕ) (S : Finset (Fin a)) :
    pathVerticesList a S ≠ [] := by simp [pathVerticesList]

theorem pathVerticesList_getElem (a : ℕ) (S : Finset (Fin a)) (i : ℕ) (hi : i < a + 1) :
    (pathVerticesList a S)[i]'(by rw [pathVerticesList_length]; exact hi) = vertexAtPos a S i := by
  simp only [pathVerticesList, List.getElem_ofFn]

/-- Consecutive vertices in the path satisfy the arc relation -/
theorem vertexAtPos_arc (a : ℕ) (S : Finset (Fin a)) (i : Fin a) :
    integerLattice.arc (vertexAtPos a S i.val) (vertexAtPos a S (i.val + 1)) := by
  simp only [vertexAtPos, eastStepCount, integerLattice]
  by_cases hi : i ∈ S
  · -- i ∈ S: east step (x increases by 1, y stays the same)
    left
    have hfilter : (S.filter (fun j => j.val < i.val + 1)).card = 
                   (S.filter (fun j => j.val < i.val)).card + 1 := by
      have heq : S.filter (fun j => j.val < i.val + 1) = 
                 insert i (S.filter (fun j => j.val < i.val)) := by
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
    constructor
    · simp only [hfilter]; push_cast; ring
    · simp only [hfilter]; push_cast; ring
  · -- i ∉ S: north step (x stays the same, y increases by 1)
    right
    have hfilter : (S.filter (fun j => j.val < i.val + 1)).card = 
                   (S.filter (fun j => j.val < i.val)).card := by
      congr 1; ext j; simp only [Finset.mem_filter]
      constructor
      · intro ⟨hj, hlt⟩
        constructor
        · exact hj
        · by_cases hji : j.val = i.val
          · exfalso; have : j = i := Fin.ext hji; rw [this] at hj; exact hi hj
          · exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) hji
      · intro ⟨hj, hlt⟩; exact ⟨hj, Nat.lt_succ_of_lt hlt⟩
    constructor
    · simp only [hfilter]
    · simp only [hfilter]; push_cast; ring

/-- Construct a path from (0, -a) to (b, -b) given a b-element subset S of Fin a -/
noncomputable def eastStepsToPath (a b : ℕ) (S : Finset (Fin a)) (_hcard : S.card = b) :
    SimpleDigraph.Path integerLattice where
  vertices := pathVerticesList a S
  nonempty := pathVerticesList_nonempty a S
  arcs_valid := by
    intro i hi
    rw [pathVerticesList_length] at hi
    have hi' : i < a := by omega
    simp only [List.get_eq_getElem]
    have h1 : i < a + 1 := by omega
    have h2 : i + 1 < a + 1 := hi
    rw [pathVerticesList_getElem a S i h1, pathVerticesList_getElem a S (i + 1) h2]
    exact vertexAtPos_arc a S ⟨i, hi'⟩

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

/-- Extract the set of east-step indices from a path.
    For a path p from (0, -a) to (b, -b), step i is east iff x increases at step i. -/
noncomputable def pathToEastSteps (a : ℕ) (p : SimpleDigraph.Path integerLattice) 
    (hlen : p.vertices.length = a + 1) : Finset (Fin a) :=
  Finset.univ.filter fun i => 
    let hi : i.val + 1 < p.vertices.length := by rw [hlen]; omega
    (p.vertices.get ⟨i.val + 1, hi⟩).1 = (p.vertices.get ⟨i.val, Nat.lt_of_succ_lt hi⟩).1 + 1

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

/-- The step list has length = vertices.length - 1 = number of arcs. -/
theorem dyckPathToSteps_length (p : SimpleDigraph.Path dyckDigraph) :
    (dyckPathToSteps p).length = p.vertices.length - 1 := by
  simp [dyckPathToSteps]

/-- Key lemma: the y-coordinate at position i equals #U - #D in the first i steps (as integers). -/
theorem dyckPath_y_eq_count_diff_int (p : SimpleDigraph.Path dyckDigraph) (i : ℕ)
    (hi : i < p.vertices.length) (hstart : p.start = (0, 0)) :
    ((p.vertices.get ⟨i, hi⟩).2 : ℤ) =
      ((dyckPathToSteps p).take i).count DyckStep.U - ((dyckPathToSteps p).take i).count DyckStep.D := by
  induction i with
  | zero =>
    simp only [List.take_zero, List.count_nil, CharP.cast_eq_zero, sub_zero]
    unfold SimpleDigraph.Path.start at hstart
    have h0 : p.vertices.get ⟨0, hi⟩ = p.vertices.head p.nonempty := by
      rw [List.get_mk_zero hi]
    rw [h0, hstart]
    rfl
  | succ j ih =>
    have hj : j < p.vertices.length := Nat.lt_of_succ_lt hi
    have ihj := ih hj
    have harc := p.arcs_valid j hi
    have hsteps_len : j < (dyckPathToSteps p).length := by
      rw [dyckPathToSteps_length]; omega
    have hstep_j : (dyckPathToSteps p)[j] =
        if (p.vertices.get ⟨j + 1, hi⟩).2 = (p.vertices.get ⟨j, hj⟩).2 + 1
        then DyckStep.U else DyckStep.D := by
      simp only [dyckPathToSteps, List.getElem_map, List.getElem_finRange, Fin.cast_mk,
        List.get_eq_getElem]
    unfold dyckDigraph at harc
    simp only at harc
    rcases harc with ⟨_, hy_up⟩ | ⟨_, hy_down, _⟩
    · have hU : (dyckPathToSteps p)[j] = DyckStep.U := by
        rw [hstep_j]; simp only [hy_up, ↓reduceIte]
      rw [List.take_succ_eq_append_getElem hsteps_len, List.count_append, List.count_append]
      simp only [List.count_singleton, hU]
      have h1 : (if (DyckStep.U == DyckStep.U) = true then 1 else 0) = 1 := by native_decide
      have h2 : (if (DyckStep.U == DyckStep.D) = true then 1 else 0) = 0 := by native_decide
      rw [h1, h2, add_zero, hy_up]; push_cast; omega
    · have heq : (p.vertices.get ⟨j, Nat.lt_of_succ_lt hi⟩).2 = (p.vertices.get ⟨j, hj⟩).2 := rfl
      rw [heq] at hy_down
      have hD : (dyckPathToSteps p)[j] = DyckStep.D := by
        rw [hstep_j]
        have hne : (p.vertices.get ⟨j + 1, hi⟩).2 ≠ (p.vertices.get ⟨j, hj⟩).2 + 1 := by omega
        simp only [hne, ↓reduceIte]
      rw [List.take_succ_eq_append_getElem hsteps_len, List.count_append, List.count_append]
      simp only [List.count_singleton, hD]
      have h1 : (if (DyckStep.D == DyckStep.U) = true then 1 else 0) = 0 := by native_decide
      have h2 : (if (DyckStep.D == DyckStep.D) = true then 1 else 0) = 1 := by native_decide
      rw [h1, h2, add_zero]; push_cast; omega

/-- Convert a Dyck path to a DyckWord.
    Each arc (x,y) → (x+1,y+1) becomes U, each arc (x,y) → (x+1,y-1) becomes D.

    **Note:** This definition requires substantial infrastructure to prove well-formedness.
    The key properties are:
    - count_U_eq_count_D: follows from start.2 = 0 = finish.2
    - count_D_le_count_U: follows from y ≥ 0 throughout the path (Dyck condition) -/
def dyckPathToWord (p : SimpleDigraph.Path dyckDigraph) (hstart : p.start = (0, 0))
    (hfinish : p.finish.2 = 0) : DyckWord where
  toList := dyckPathToSteps p
  count_U_eq_count_D := by
    -- The number of U steps equals the number of D steps because we start and end at y = 0
    -- Each U increases y by 1, each D decreases y by 1
    -- So #U - #D = final_y - initial_y = 0 - 0 = 0
    have hlen : p.vertices.length ≥ 1 := List.length_pos_of_ne_nil p.nonempty
    have hlast : p.vertices.length - 1 < p.vertices.length := Nat.sub_lt hlen Nat.one_pos
    have hfinish_eq : p.finish = p.vertices.get ⟨p.vertices.length - 1, hlast⟩ := by
      unfold SimpleDigraph.Path.finish
      rw [List.getLast_eq_getElem]
      rfl
    have hy := dyckPath_y_eq_count_diff_int p (p.vertices.length - 1) hlast hstart
    have hsteps_len : (dyckPathToSteps p).length = p.vertices.length - 1 := dyckPathToSteps_length p
    have htake : (dyckPathToSteps p).take (p.vertices.length - 1) = dyckPathToSteps p := by
      conv_lhs => rw [← hsteps_len]
      exact List.take_length
    rw [htake] at hy
    rw [hfinish_eq] at hfinish
    have hfinish' : (p.vertices.get ⟨p.vertices.length - 1, hlast⟩).2 = 0 := hfinish
    rw [hfinish'] at hy
    simp only [CharP.cast_eq_zero] at hy
    omega
  count_D_le_count_U := by
    -- At any prefix, #D ≤ #U because y ≥ 0 throughout the path
    -- y = #U - #D, so #D ≤ #U ⟺ y ≥ 0
    intro i
    by_cases hi : i < p.vertices.length
    · have hy := dyckPath_y_eq_count_diff_int p i hi hstart
      -- The y-coordinate is always ≥ 0 (since it's a ℕ)
      -- So count U - count D ≥ 0, i.e., count D ≤ count U
      have hy_nonneg : (0 : ℤ) ≤ (p.vertices.get ⟨i, hi⟩).2 := Int.natCast_nonneg _
      omega
    · -- If i ≥ vertices.length, then take i = full list
      have hsteps_len : (dyckPathToSteps p).length = p.vertices.length - 1 := dyckPathToSteps_length p
      have htake : (dyckPathToSteps p).take i = dyckPathToSteps p := by
        apply List.take_of_length_le
        omega
      rw [htake]
      -- For the full list, count_U = count_D (from above), so count_D ≤ count_U
      have hlen : p.vertices.length ≥ 1 := List.length_pos_of_ne_nil p.nonempty
      have hlast : p.vertices.length - 1 < p.vertices.length := Nat.sub_lt hlen Nat.one_pos
      have hy := dyckPath_y_eq_count_diff_int p (p.vertices.length - 1) hlast hstart
      have htake' : (dyckPathToSteps p).take (p.vertices.length - 1) = dyckPathToSteps p := by
        conv_lhs => rw [← hsteps_len]
        exact List.take_length
      rw [htake'] at hy
      have hy_nonneg : (0 : ℤ) ≤ (p.vertices.get ⟨p.vertices.length - 1, hlast⟩).2 :=
        Int.natCast_nonneg _
      omega

/-- Helper function to compute the y-coordinate at position i in a DyckWord path -/
def dyckWordY (w : DyckWord) (i : ℕ) : ℕ :=
  (w.toList.take i).count DyckStep.U - (w.toList.take i).count DyckStep.D

/-- Convert a DyckWord to a list of vertices -/
def dyckWordToVertices (w : DyckWord) : List (ℤ × ℕ) :=
  (List.finRange (w.toList.length + 1)).map fun ⟨i, _⟩ => ((i : ℤ), dyckWordY w i)

theorem dyckWordToVertices_length (w : DyckWord) : (dyckWordToVertices w).length = w.toList.length + 1 := by
  simp [dyckWordToVertices]

theorem dyckWordToVertices_nonempty (w : DyckWord) : dyckWordToVertices w ≠ [] := by
  intro h
  have := dyckWordToVertices_length w
  rw [h] at this
  simp at this

theorem dyckWordToVertices_getElem (w : DyckWord) (i : ℕ) (hi : i < (dyckWordToVertices w).length) :
    (dyckWordToVertices w)[i] = ((i : ℤ), dyckWordY w i) := by
  simp [dyckWordToVertices]

/-- Key lemma: if we take a D step at position i, then y > 0 at position i -/
theorem dyckWord_y_pos_before_D (w : DyckWord) (i : ℕ) (hi : i < w.toList.length)
    (hD : w.toList[i] = DyckStep.D) : 0 < dyckWordY w i := by
  unfold dyckWordY
  have hle := w.count_D_le_count_U i
  have hle' := w.count_D_le_count_U (i + 1)
  have htake_succ : w.toList.take (i + 1) = w.toList.take i ++ [w.toList[i]] := by
    rw [List.take_succ_eq_append_getElem hi]
  rw [htake_succ, List.count_append, List.count_append, List.count_singleton,
      List.count_singleton] at hle'
  simp only [hD] at hle'
  have h1 : (if (DyckStep.D == DyckStep.D) = true then 1 else 0) = 1 := by native_decide
  have h2 : (if (DyckStep.D == DyckStep.U) = true then 1 else 0) = 0 := by native_decide
  simp only [h1, h2, add_zero] at hle'
  omega

/-- Convert a DyckWord to a Dyck path from (0, 0) to (2n, 0) where n = semilength.

    **Note:** The vertices are constructed as (i, y_i) where y_i = #U - #D in the first i steps.
    The Dyck word conditions ensure y_i ≥ 0 and the path stays in the valid region. -/
def dyckWordToPath (w : DyckWord) : SimpleDigraph.Path dyckDigraph where
  vertices := dyckWordToVertices w
  nonempty := dyckWordToVertices_nonempty w
  arcs_valid := by
    intro i hi
    rw [dyckWordToVertices_length] at hi
    have hi' : i < w.toList.length := by omega
    have hi1 : i + 1 < (dyckWordToVertices w).length := by rw [dyckWordToVertices_length]; omega
    have hi0 : i < (dyckWordToVertices w).length := by omega
    simp only [List.get_eq_getElem]
    rw [dyckWordToVertices_getElem w i hi0, dyckWordToVertices_getElem w (i + 1) hi1]
    have hstep : w.toList[i] = DyckStep.U ∨ w.toList[i] = DyckStep.D := DyckStep.dichotomy _
    unfold dyckWordY
    have htake_succ : w.toList.take (i + 1) = w.toList.take i ++ [w.toList[i]] := by
      rw [List.take_succ_eq_append_getElem hi']
    rcases hstep with hU | hD
    · -- U step: y increases by 1
      left
      constructor
      · push_cast; ring
      · rw [htake_succ, List.count_append, List.count_append, List.count_singleton,
            List.count_singleton]
        simp only [hU]
        have h1 : (if (DyckStep.U == DyckStep.U) = true then 1 else 0) = 1 := by native_decide
        have h2 : (if (DyckStep.U == DyckStep.D) = true then 1 else 0) = 0 := by native_decide
        simp only [h1, h2, add_zero]
        have hle := w.count_D_le_count_U i
        omega
    · -- D step: y decreases by 1
      right
      constructor
      · push_cast; ring
      constructor
      · rw [htake_succ, List.count_append, List.count_append, List.count_singleton,
            List.count_singleton]
        simp only [hD]
        have h1 : (if (DyckStep.D == DyckStep.D) = true then 1 else 0) = 1 := by native_decide
        have h2 : (if (DyckStep.D == DyckStep.U) = true then 1 else 0) = 0 := by native_decide
        simp only [h1, h2, add_zero]
        have hle := w.count_D_le_count_U i
        have hle' := w.count_D_le_count_U (i + 1)
        rw [htake_succ, List.count_append, List.count_append, List.count_singleton,
            List.count_singleton] at hle'
        simp only [hD, h1, h2, add_zero] at hle'
        omega
      · exact dyckWord_y_pos_before_D w i hi' hD

/-- Translation function for vertices in the Dyck digraph -/
def translateVertex (d : ℤ) (v : ℤ × ℕ) : ℤ × ℕ := (v.1 + d, v.2)

/-- Translation preserves dyckDigraph arcs -/
theorem dyckDigraph_arc_translate (d : ℤ) (u v : ℤ × ℕ) :
    dyckDigraph.arc u v ↔ dyckDigraph.arc (translateVertex d u) (translateVertex d v) := by
  unfold dyckDigraph translateVertex
  simp only
  constructor
  · intro h
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy, hpos⟩
    · left; constructor <;> omega
    · right; constructor; omega; constructor; omega; exact hpos
  · intro h
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy, hpos⟩
    · left; constructor <;> omega
    · right; refine ⟨?_, ?_, hpos⟩ <;> omega

/-- Create translated path by shifting x-coordinates -/
def translatePath (d : ℤ) (p : SimpleDigraph.Path dyckDigraph) :
    SimpleDigraph.Path dyckDigraph where
  vertices := p.vertices.map (translateVertex d)
  nonempty := by simp [p.nonempty]
  arcs_valid := by
    intro k hk
    simp only [List.length_map] at hk
    have hk' : k < p.vertices.length := Nat.lt_of_succ_lt hk
    have hk'' : k + 1 < p.vertices.length := hk
    -- Need to show arc at position k in the mapped list
    -- vertices.get ⟨k, _⟩ = (vertices.map f).get ⟨k, _⟩ = f (vertices.get ⟨k, _⟩)
    have h1 : (p.vertices.map (translateVertex d)).get ⟨k, by simp; exact hk'⟩ = 
              translateVertex d (p.vertices.get ⟨k, hk'⟩) := by
      simp [List.get_eq_getElem]
    have h2 : (p.vertices.map (translateVertex d)).get ⟨k + 1, by simp; exact hk''⟩ = 
              translateVertex d (p.vertices.get ⟨k + 1, hk''⟩) := by
      simp [List.get_eq_getElem]
    rw [h1, h2]
    rw [← dyckDigraph_arc_translate d]
    exact p.arcs_valid k hk
/-!
### Nested Dyck Paths for the Catalan Hankel Determinant

The nested Dyck path from (-2n, 0) to (2n, 0) goes:
(-2n, 0) → (-2n+1, 1) → ... → (0, 2n) → (1, 2n-1) → ... → (2n, 0)

At step i (0 ≤ i ≤ 4n), the vertex is (i - 2n, min(i, 4n - i)).
-/


/-- The vertices of the nested Dyck path from (-2n, 0) to (2n, 0) -/
def nestedDyckVertices (n : ℕ) : List (ℤ × ℕ) :=
  (List.finRange (4 * n + 1)).map fun ⟨i, _⟩ =>
    ((i : ℤ) - 2 * n, min i (4 * n - i))

theorem nestedDyckVertices_nonempty (n : ℕ) : nestedDyckVertices n ≠ [] := by
  simp [nestedDyckVertices]

theorem nestedDyckVertices_length (n : ℕ) : (nestedDyckVertices n).length = 4 * n + 1 := by
  simp [nestedDyckVertices]

theorem nestedDyckVertices_getElem (n : ℕ) (i : ℕ) (hi : i < (nestedDyckVertices n).length) :
    (nestedDyckVertices n)[i] = ((i : ℤ) - 2 * n, min i (4 * n - i)) := by
  simp only [nestedDyckVertices, List.getElem_map, List.getElem_finRange]
  rfl

theorem nestedDyckVertices_arcs_valid (n : ℕ) :
    ∀ i : ℕ, ∀ hi : i + 1 < (nestedDyckVertices n).length,
      dyckDigraph.arc ((nestedDyckVertices n).get ⟨i, Nat.lt_of_succ_lt hi⟩)
        ((nestedDyckVertices n).get ⟨i + 1, hi⟩) := by
  intro i hi
  have hlen : (nestedDyckVertices n).length = 4 * n + 1 := nestedDyckVertices_length n
  rw [hlen] at hi
  simp only [List.get_eq_getElem, nestedDyckVertices_getElem n i (by rw [hlen]; omega),
             nestedDyckVertices_getElem n (i + 1) (by rw [hlen]; exact hi)]
  unfold dyckDigraph
  simp only
  by_cases hcase : i < 2 * n
  · left
    constructor
    · push_cast; ring
    · have h1 : min i (4 * n - i) = i := Nat.min_eq_left (by omega)
      have h2 : min (i + 1) (4 * n - (i + 1)) = i + 1 := Nat.min_eq_left (by omega)
      rw [h1, h2]
  · push Not at hcase
    right
    constructor
    · push_cast; ring
    constructor
    · have h1 : min i (4 * n - i) = 4 * n - i := Nat.min_eq_right (by omega)
      have h2 : min (i + 1) (4 * n - (i + 1)) = 4 * n - i - 1 := Nat.min_eq_right (by omega)
      rw [h1, h2]; omega
    · have h1 : min i (4 * n - i) = 4 * n - i := Nat.min_eq_right (by omega)
      rw [h1]; omega

/-- The nested Dyck path from (-2n, 0) to (2n, 0) -/
def nestedDyckPath (n : ℕ) : SimpleDigraph.Path dyckDigraph where
  vertices := nestedDyckVertices n
  nonempty := nestedDyckVertices_nonempty n
  arcs_valid := nestedDyckVertices_arcs_valid n
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

/-- Apply a step to a lattice point -/
def LatticeStep'.apply (s : LatticeStep') (p : ℤ × ℤ) : ℤ × ℤ :=
  match s with
  | east => (p.1 + 1, p.2)
  | north => (p.1, p.2 + 1)

/-- A lattice path as a list of steps (matching LGV1.lean's definition) -/
abbrev LatticePath' := List LatticeStep'

/-- Compute the endpoint of a lattice path starting from a given point -/
def LatticePath'.endpoint (path : LatticePath') (start : ℤ × ℤ) : ℤ × ℤ :=
  path.foldl (fun p s => s.apply p) start

/-- Compute all vertices visited by a lattice path, including start.
    For path = [s₁, s₂, ..., sₙ], this returns [start, s₁(start), s₂(s₁(start)), ...] -/
def LatticePath'.toVertices (path : LatticePath') (start : ℤ × ℤ) : List (ℤ × ℤ) :=
  match path with
  | [] => [start]
  | s :: rest => start :: LatticePath'.toVertices rest (s.apply start)

/-- The vertices list is nonempty -/
theorem LatticePath'.toVertices_nonempty (path : LatticePath') (start : ℤ × ℤ) :
    (LatticePath'.toVertices path start) ≠ [] := by
  cases path <;> simp [toVertices]

/-- Each step creates a valid arc in the integer lattice -/
theorem LatticeStep'.apply_creates_arc (s : LatticeStep') (p : ℤ × ℤ) :
    integerLattice.arc p (s.apply p) := by
  cases s with
  | east => 
    simp only [apply, integerLattice]
    left
    simp
  | north => 
    simp only [apply, integerLattice]
    right
    simp

/-- Consecutive vertices in toVertices are connected by arcs -/
theorem LatticePath'.toVertices_arcs_valid (path : LatticePath') (start : ℤ × ℤ) :
    ∀ i : ℕ, ∀ hi : i + 1 < (LatticePath'.toVertices path start).length,
      integerLattice.arc ((LatticePath'.toVertices path start).get ⟨i, Nat.lt_of_succ_lt hi⟩)
        ((LatticePath'.toVertices path start).get ⟨i + 1, hi⟩) := by
  induction path generalizing start with
  | nil => intro i hi; simp [toVertices] at hi
  | cons s rest ih =>
    intro i hi
    simp only [toVertices] at hi ⊢
    cases i with
    | zero =>
      simp only [List.get_eq_getElem, List.getElem_cons_zero,
                 List.getElem_cons_succ]
      cases rest with
      | nil =>
        simp only [toVertices, List.getElem_singleton]
        exact LatticeStep'.apply_creates_arc s start
      | cons s' rest' =>
        simp only [toVertices, List.getElem_cons_zero]
        exact LatticeStep'.apply_creates_arc s start
    | succ j =>
      simp only [List.get_eq_getElem, List.getElem_cons_succ] at hi ⊢
      simp only [List.length_cons] at hi
      exact ih (s.apply start) j (by omega : j + 1 < (LatticePath'.toVertices rest (s.apply start)).length)

/-- Convert a lattice path to a SimpleDigraph.Path -/
noncomputable def LatticePath'.toPath (path : LatticePath') (start : ℤ × ℤ) : 
    SimpleDigraph.Path integerLattice where
  vertices := LatticePath'.toVertices path start
  nonempty := LatticePath'.toVertices_nonempty path start
  arcs_valid := LatticePath'.toVertices_arcs_valid path start

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
/-!
### Surjectivity of toPath

To complete the bridge between path representations, we need to show that every
`SimpleDigraph.Path` in the integer lattice comes from a `LatticePath'`.

The key insight is that each arc in the integer lattice uniquely determines a step:
- If v.1 = u.1 + 1 (and v.2 = u.2), the step is east
- If v.2 = u.2 + 1 (and v.1 = u.1), the step is north
-/


/-- Convert an arc in the integer lattice to a step.
    This is the inverse operation to LatticeStep'.apply. -/
def arcToStep' (u v : ℤ × ℤ) (_h : integerLattice.arc u v) : LatticeStep' :=
  if v.1 = u.1 + 1 then LatticeStep'.east else LatticeStep'.north

/-- arcToStep' produces the correct step -/
theorem arcToStep'_apply (u v : ℤ × ℤ) (h : integerLattice.arc u v) :
    (arcToStep' u v h).apply u = v := by
  unfold arcToStep' LatticeStep'.apply
  simp only [integerLattice] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [h1, ↓reduceIte]
    ext <;> simp [h1, h2]
  · simp only [h1]
    ext <;> simp [h1, h2]

/-- Convert a vertex list to a step list (partial inverse of toVertices) -/
def verticesToSteps' : (vs : List (ℤ × ℤ)) → 
    (harcs : ∀ i : ℕ, ∀ hi : i + 1 < vs.length, 
      integerLattice.arc (vs.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vs.get ⟨i + 1, hi⟩)) → 
    LatticePath'
  | [], _ => []
  | [_], _ => []
  | u :: v :: rest, harcs => 
    let h : integerLattice.arc u v := harcs 0 (by simp)
    arcToStep' u v h :: verticesToSteps' (v :: rest) (fun i hi => harcs (i + 1) (by simp at hi ⊢; omega))

/-- Convert a SimpleDigraph.Path to a LatticePath' -/
def pathToLatticePath' (p : SimpleDigraph.Path integerLattice) : LatticePath' :=
  verticesToSteps' p.vertices p.arcs_valid

/-- verticesToSteps' produces the correct vertex list when applied to the original vertices -/
theorem verticesToSteps'_toVertices (vs : List (ℤ × ℤ)) (hne : vs ≠ [])
    (harcs : ∀ i : ℕ, ∀ hi : i + 1 < vs.length, 
      integerLattice.arc (vs.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vs.get ⟨i + 1, hi⟩)) :
    LatticePath'.toVertices (verticesToSteps' vs harcs) (vs.head hne) = vs := by
  induction vs with
  | nil => contradiction
  | cons u rest ih =>
    cases rest with
    | nil => simp [verticesToSteps', LatticePath'.toVertices]
    | cons v rest' =>
      simp only [verticesToSteps', LatticePath'.toVertices, List.head_cons, List.cons.injEq, true_and]
      have h_arc : integerLattice.arc u v := harcs 0 (by simp)
      have h_apply : (arcToStep' u v h_arc).apply u = v := arcToStep'_apply u v h_arc
      rw [h_apply]
      have harcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v :: rest').length, 
          integerLattice.arc ((v :: rest').get ⟨i, Nat.lt_of_succ_lt hi⟩) 
            ((v :: rest').get ⟨i + 1, hi⟩) := fun i hi => harcs (i + 1) (by simp at hi ⊢; omega)
      exact ih (by simp) harcs'

/-- The bijection between LatticePath' and SimpleDigraph.Path starting at a fixed point.
    
    This establishes that the two path representations are equivalent, which is the key
    step needed to bridge LGV1.lean's counting results with LGV2.lean's weighted results. -/
noncomputable def latticePath'Equiv (start : ℤ × ℤ) :
    LatticePath' ≃ { p : SimpleDigraph.Path integerLattice // p.start = start } where
  toFun path := ⟨LatticePath'.toPath path start, LatticePath'.toPath_start path start⟩
  invFun p := pathToLatticePath' p.val
  left_inv path := by
    have h := LatticePath'.toPath_injective start
    apply h
    simp only [LatticePath'.toPath, pathToLatticePath']
    apply SimpleDigraph.Path.ext_vertices'
    have := verticesToSteps'_toVertices (LatticePath'.toVertices path start) 
      (LatticePath'.toVertices_nonempty path start) (LatticePath'.toVertices_arcs_valid path start)
    simp only [LatticePath'.toVertices_head] at this
    exact this
  right_inv p := by
    have hstart : p.val.start = start := p.property
    apply Subtype.ext
    simp only [LatticePath'.toPath, pathToLatticePath']
    apply SimpleDigraph.Path.ext_vertices'
    have := verticesToSteps'_toVertices p.val.vertices p.val.nonempty p.val.arcs_valid
    simp only [SimpleDigraph.Path.start] at this hstart
    rw [hstart] at this
    exact this
/-!
### Path Tuple Bridge

This section provides the bridge between LGV1-style path tuples (using LatticePath = List LatticeStep)
and LGV2-style path tuples (using SimpleDigraph.Path).

The key results are:
1. `latticePath'TupleEquiv` - bijection between path tuples
2. `latticePath'Tuple_isIntersecting_iff` - intersection property is preserved

These results allow us to transfer the counting result `sum_signed_ipatFinset_card_eq_zero`
from LGV2 types to LGV1 types.
-/


/-- A path tuple in the LGV1 style: k paths from A to B where each path is a list of steps. -/
structure LatticePath'Tuple (k : ℕ) (A B : kVertex (ℤ × ℤ) k) where
  /-- The paths in the tuple -/
  paths : Fin k → LatticePath'
  /-- Each path goes from A_i to B_i -/
  valid : ∀ i, LatticePath'.endpoint (paths i) (A i) = B i

@[ext]
theorem LatticePath'Tuple.ext {k : ℕ} {A B : kVertex (ℤ × ℤ) k} 
    {pt1 pt2 : LatticePath'Tuple k A B} (h : ∀ i, pt1.paths i = pt2.paths i) : pt1 = pt2 := by
  cases pt1; cases pt2
  simp only [mk.injEq]
  funext i
  exact h i

/-- The vertices visited by a path in a LatticePath'Tuple -/
def LatticePath'Tuple.verticesOf {k : ℕ} {A B : kVertex (ℤ × ℤ) k} 
    (pt : LatticePath'Tuple k A B) (i : Fin k) : Set (ℤ × ℤ) :=
  { p | p ∈ LatticePath'.toVertices (pt.paths i) (A i) }

/-- A LatticePath'Tuple is non-intersecting if no two paths share a vertex -/
def LatticePath'Tuple.isNonIntersecting {k : ℕ} {A B : kVertex (ℤ × ℤ) k} 
    (pt : LatticePath'Tuple k A B) : Prop :=
  ∀ i j, i ≠ j → Disjoint (pt.verticesOf i) (pt.verticesOf j)

/-- A LatticePath'Tuple is intersecting if it is not non-intersecting -/
def LatticePath'Tuple.isIntersecting {k : ℕ} {A B : kVertex (ℤ × ℤ) k} 
    (pt : LatticePath'Tuple k A B) : Prop :=
  ¬pt.isNonIntersecting

/-- Convert a LatticePath'Tuple to a PathTuple -/
noncomputable def latticePath'TupleToPathTuple {k : ℕ} {A B : kVertex (ℤ × ℤ) k}
    (pt : LatticePath'Tuple k A B) : PathTuple integerLattice k A B where
  paths := fun i => LatticePath'.toPath (pt.paths i) (A i)
  starts := fun i => LatticePath'.toPath_start (pt.paths i) (A i)
  finishes := fun i => by
    rw [LatticePath'.toPath_finish]
    exact pt.valid i

/-- Convert a PathTuple to a LatticePath'Tuple -/
noncomputable def pathTupleToLatticePath'Tuple {k : ℕ} {A B : kVertex (ℤ × ℤ) k}
    (pt : PathTuple integerLattice k A B) : LatticePath'Tuple k A B where
  paths := fun i => pathToLatticePath' (pt.paths i)
  valid := fun i => by
    have h := verticesToSteps'_toVertices (pt.paths i).vertices (pt.paths i).nonempty (pt.paths i).arcs_valid
    have hstart : (pt.paths i).start = A i := pt.starts i
    have hfinish : (pt.paths i).finish = B i := pt.finishes i
    simp only [SimpleDigraph.Path.start] at hstart
    simp only [SimpleDigraph.Path.finish] at hfinish
    unfold pathToLatticePath'
    -- The endpoint is computed by foldl, which equals the last vertex
    have h_toVertices : LatticePath'.toVertices (verticesToSteps' (pt.paths i).vertices (pt.paths i).arcs_valid) 
        ((pt.paths i).vertices.head (pt.paths i).nonempty) = (pt.paths i).vertices := h
    rw [hstart] at h_toVertices
    have h_endpoint : LatticePath'.endpoint (verticesToSteps' (pt.paths i).vertices (pt.paths i).arcs_valid) (A i) =
        ((pt.paths i).vertices.getLast (pt.paths i).nonempty) := by
      rw [← LatticePath'.toVertices_getLast]
      simp only [h_toVertices]
    unfold LatticePath'.endpoint at h_endpoint ⊢
    rw [h_endpoint, hfinish]

/-- The bijection between LatticePath'Tuple and PathTuple -/
noncomputable def latticePath'TupleEquiv {k : ℕ} (A B : kVertex (ℤ × ℤ) k) :
    LatticePath'Tuple k A B ≃ PathTuple integerLattice k A B where
  toFun := latticePath'TupleToPathTuple
  invFun := pathTupleToLatticePath'Tuple
  left_inv pt := by
    apply LatticePath'Tuple.ext
    intro i
    simp only [pathTupleToLatticePath'Tuple, latticePath'TupleToPathTuple]
    -- Need to show: pathToLatticePath' (LatticePath'.toPath (pt.paths i) (A i)) = pt.paths i
    have h := LatticePath'.toPath_injective (A i)
    apply h
    simp only [LatticePath'.toPath, pathToLatticePath']
    apply SimpleDigraph.Path.ext_vertices'
    have := verticesToSteps'_toVertices (LatticePath'.toVertices (pt.paths i) (A i)) 
      (LatticePath'.toVertices_nonempty (pt.paths i) (A i)) 
      (LatticePath'.toVertices_arcs_valid (pt.paths i) (A i))
    simp only [LatticePath'.toVertices_head] at this
    exact this
  right_inv pt := by
    apply PathTuple.ext
    intro i
    simp only [latticePath'TupleToPathTuple, pathTupleToLatticePath'Tuple]
    -- Need to show: LatticePath'.toPath (pathToLatticePath' (pt.paths i)) (A i) = pt.paths i
    simp only [LatticePath'.toPath, pathToLatticePath']
    apply SimpleDigraph.Path.ext_vertices'
    have := verticesToSteps'_toVertices (pt.paths i).vertices (pt.paths i).nonempty (pt.paths i).arcs_valid
    have hstart : (pt.paths i).start = A i := pt.starts i
    simp only [SimpleDigraph.Path.start] at this hstart
    rw [hstart] at this
    exact this

end LGV

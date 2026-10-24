/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import sympy.matrices.determinants.LGV2
/-!
# The Lindström-Gessel-Viennot Lemma: Part 1

This file formalizes the first part of the Lindström-Gessel-Viennot (LGV) lemma,
covering the basic definitions and counting results for lattice paths.

## Main definitions

* `LGV1.LatticePoint` - A point on the integer lattice ℤ²
* `LGV1.integerLattice` - The integer lattice as a Mathlib `Digraph`
* `LGV1.LatticePath` - A path on the integer lattice using only east (right) and north (up) steps
* `LGV1.LatticePath.stepCount` - The total number of steps in a path
* `LGV1.LatticePath.eastStepCount` - The number of east steps in a path
* `LGV1.PathTuple` - A k-tuple of lattice paths from k source vertices to k target vertices
* `LGV1.PathTuple.isNonIntersecting` - Property that no two paths share a vertex (nipat)
* `LGV1.PathTuple.isIntersecting` - Property that some two paths share a vertex (ipat)
* `LGV1.kVertex` - A k-tuple of lattice points

## Main results

* `latticePath_count` - Number of paths from (a,b) to (c,d) equals C(c+d-a-b, c-a)
  (Proposition prop.lgv.1-paths.ct)
* `lgv_two_paths` - LGV lemma for k=2: determinant equals #nipats to (B,B') - #nipats to (B',B)
  (Proposition prop.lgv.2paths.count)
* `baby_jordan_curve` - Paths from A to B' and A' to B must intersect under NW conditions
  (Proposition prop.lgv.jordan-2)
* `binom_log_concave` - C(n,k)² ≥ C(n,k-1)·C(n,k+1)
  (Corollary cor.lgv.binom-unimod)
* `lgv_k_paths` - General LGV lemma: determinant equals signed sum of nipat counts
  (Proposition prop.lgv.kpaths.count)

## References

* Source: AlgebraicCombinatorics/tex/Determinants/LGV1.tex (sec.det.comb.lgv)

## Implementation notes

We formalize lattice paths as lists of steps (east or north), rather than as sequences
of vertices. This makes it easier to work with path concatenation and step counting.

The LGV lemma relates determinants to non-intersecting lattice paths. The key insight
is a sign-reversing involution that cancels intersecting path tuples.

### Relationship with LGV2.lean

This file (LGV1.lean) and LGV2.lean both work with the integer lattice digraph, but
use different representations:

- **LGV1.lean**: Uses Mathlib's `Digraph` type and `LatticePath` (list of steps: east/north)
- **LGV2.lean**: Uses `LGV.SimpleDigraph` (custom structure with irreflexivity) and
  `SimpleDigraph.Path` (list of vertices)

The integer lattice definitions have equivalent adjacency relations:
- LGV1: `integerLattice_adj_iff p q : integerLattice.Adj p q ↔ q = (p.1 + 1, p.2) ∨ q = (p.1, p.2 + 1)`
- LGV2: `integerLattice_arc_iff u v : integerLattice.arc u v ↔ v = (u.1 + 1, u.2) ∨ v = (u.1, u.2 + 1)`

### LatticeStep and LatticePath equivalence

Both files define a `LatticeStep` type for representing east/north steps:
- `LGV1.LatticeStep` (this file)
- `LGV.LatticeStep'` (in LGV2.lean)

These are equivalent types, with explicit conversion functions:
- `latticeStepEquiv : LatticeStep ≃ LGV.LatticeStep'`
- `latticePathToLatticePath' : LatticePath → LGV.LatticePath'`
- `latticePath'ToLatticePath : LGV.LatticePath' → LatticePath`

The duplication exists because LGV1 imports LGV2, preventing LGV2 from referencing
LGV1's definitions. Both definitions are kept compatible with trivial conversions.

LGV2.lean contains the complete weighted LGV lemma proof. This file contains the
counting case infrastructure with lattice-specific path counting results.
-/


open Finset BigOperators Matrix

namespace LGV1
/-!
## The Integer Lattice (Definition def.lgv.lattice)

The integer lattice ℤ² is an infinite digraph with vertices at integer points
and directed edges (arcs) going east (i,j) → (i+1,j) and north (i,j) → (i,j+1).

This digraph is acyclic and path-finite (only finitely many paths between any two points).

### Formalization of Definition def.lgv.lattice

From the TeX source (AlgebraicCombinatorics/tex/Determinants/LGV1.tex):

> We consider the infinite simple digraph with vertex set ℤ² (so the vertices are pairs
> of integers) and arcs:
>   (i,j) → (i+1,j)  for all (i,j) ∈ ℤ²  [east-steps/right-steps]
>   (i,j) → (i,j+1)  for all (i,j) ∈ ℤ²  [north-steps/up-steps]

The entire digraph is denoted by ℤ² and called the "integer lattice" or "integer grid".
-/


/-- A point on the integer lattice ℤ².
    The vertices of the integer lattice are pairs of integers.
    Label: def.lgv.lattice -/
abbrev LatticePoint := ℤ × ℤ

/-- The x-coordinate of a lattice point. -/
def LatticePoint.x (p : LatticePoint) : ℤ := p.1

/-- The y-coordinate of a lattice point. -/
def LatticePoint.y (p : LatticePoint) : ℤ := p.2

/-- The coordinate sum of a lattice point (x + y). -/
def LatticePoint.coordSum (p : LatticePoint) : ℤ := p.1 + p.2
/-!
### The Integer Lattice as a Digraph

We formalize the integer lattice as a `Digraph` instance, where an arc exists from
vertex `p` to vertex `q` if and only if `q` is obtained from `p` by either:
- An east step: q = (p.1 + 1, p.2)
- A north step: q = (p.1, p.2 + 1)
-/


/-- The adjacency relation for the integer lattice digraph.
    There is an arc from p to q iff q is one step east or north of p.
    Label: eq.def.lgv.lattice.east, eq.def.lgv.lattice.north -/
def IntegerLatticeAdj (p q : LatticePoint) : Prop :=
  q = (p.1 + 1, p.2) ∨ q = (p.1, p.2 + 1)

/-- The integer lattice as a digraph.
    This is the digraph with vertex set ℤ² and arcs (i,j) → (i+1,j) and (i,j) → (i,j+1).
    Label: def.lgv.lattice -/
def integerLattice : Digraph LatticePoint where
  Adj := IntegerLatticeAdj

/-- Decidability of adjacency in the integer lattice. -/
instance : DecidableRel IntegerLatticeAdj :=
  fun p q => decidable_of_iff
    ((q.1 = p.1 + 1 ∧ q.2 = p.2) ∨ (q.1 = p.1 ∧ q.2 = p.2 + 1))
    (by simp only [IntegerLatticeAdj, Prod.ext_iff])
/-!
## Lattice Steps and Paths

A step on the lattice is either east (right) or north (up).
A lattice path is a sequence of steps starting from a given point.

We formalize paths as lists of steps rather than lists of vertices, which makes
it easier to work with path concatenation and step counting.
-/


/-- A step on the integer lattice: either east (right) or north (up).
    - east: (i,j) → (i+1,j)
    - north: (i,j) → (i,j+1)
    
    This type is equivalent to `LGV.LatticeStep'` defined in LGV2.lean.
    The equivalence is provided by `latticeStepEquiv : LatticeStep ≃ LGV.LatticeStep'`.
    
    Label: eq.def.lgv.lattice.east, eq.def.lgv.lattice.north -/
inductive LatticeStep : Type
  | east : LatticeStep  -- (i,j) → (i+1,j)
  | north : LatticeStep -- (i,j) → (i,j+1)
  deriving DecidableEq, Repr

instance : Fintype LatticeStep where
  elems := {LatticeStep.east, LatticeStep.north}
  complete := by
    rintro ⟨⟩
    · simp [Finset.mem_insert, Finset.mem_singleton]
    · simp [Finset.mem_insert, Finset.mem_singleton]

/-- Apply a step to a lattice point. -/
def LatticeStep.apply (s : LatticeStep) (p : LatticePoint) : LatticePoint :=
  match s with
  | east => (p.1 + 1, p.2)
  | north => (p.1, p.2 + 1)

/-- A lattice path is a list of steps.
    
    This type is equivalent to `LGV.LatticePath'` defined in LGV2.lean.
    Conversion functions are provided:
    - `latticePathToLatticePath' : LatticePath → LGV.LatticePath'`
    - `latticePath'ToLatticePath : LGV.LatticePath' → LatticePath`
    - `latticePathToLatticePath'_endpoint` proves endpoint preservation -/
abbrev LatticePath := List LatticeStep

/-- The endpoint of a path starting from a given point. -/
def LatticePath.endpoint (path : LatticePath) (start : LatticePoint) : LatticePoint :=
  path.foldl (fun p s => s.apply p) start


/-- The endpoint of appended paths: endpoint(p1 ++ p2, A) = endpoint(p2, endpoint(p1, A)). -/
theorem LatticePath.endpoint_append (path1 path2 : LatticePath) (start : LatticePoint) :
    LatticePath.endpoint (path1 ++ path2) start =
    LatticePath.endpoint path2 (LatticePath.endpoint path1 start) := by
  unfold LatticePath.endpoint
  rw [List.foldl_append]
def LatticePath.stepCount (path : LatticePath) : ℕ := path.length

/-- The number of east steps in a path. -/
def LatticePath.eastStepCount (path : LatticePath) : ℕ :=
  path.count LatticeStep.east

/-- The number of north steps in a path. -/
def LatticePath.northStepCount (path : LatticePath) : ℕ :=
  path.count LatticeStep.north

/-- All vertices visited by a path, including start and end. -/
def LatticePath.vertices (path : LatticePath) (start : LatticePoint) : List LatticePoint :=
  start :: path.scanl (fun p s => s.apply p) start |>.tail

/-- Check if a path goes from point a to point b. -/
def LatticePath.isPathFromTo (path : LatticePath) (a b : LatticePoint) : Prop :=
  path.endpoint a = b

/-- If a path goes from A to B, then take n goes from A to an intermediate point,
    and drop n goes from that point to B. -/
theorem LatticePath.isPathFromTo_take_drop (path : LatticePath) (n : ℕ) (A B : LatticePoint)
    (h : LatticePath.isPathFromTo path A B) :
    let mid := LatticePath.endpoint (path.take n) A
    LatticePath.isPathFromTo (path.take n) A mid ∧ LatticePath.isPathFromTo (path.drop n) mid B := by
  constructor
  · rfl
  · unfold LatticePath.isPathFromTo at h ⊢
    have key : LatticePath.endpoint (path.take n ++ path.drop n) A = LatticePath.endpoint path A := by
      rw [List.take_append_drop]
    rw [endpoint_append] at key
    rw [key, h]

/-- If head goes A→v and tail goes v→B, then head ++ tail goes A→B. -/
theorem LatticePath.isPathFromTo_append (head tail : LatticePath) (A v B : LatticePoint)
    (hhead : LatticePath.isPathFromTo head A v) (htail : LatticePath.isPathFromTo tail v B) :
    LatticePath.isPathFromTo (head ++ tail) A B := by
  unfold LatticePath.isPathFromTo at *
  rw [endpoint_append, hhead, htail]
/-!
## Counting Paths (Proposition prop.lgv.1-paths.ct)

The number of lattice paths from (a,b) to (c,d) is:
- C(c+d-a-b, c-a) if c+d ≥ a+b (i.e., d-b ≥ a-c)
- 0 if c+d < a+b

This follows from:
- Observation 1: Each path has exactly c+d-a-b steps
- Observation 2: Each path has exactly c-a east steps
- Observation 3: A path with these counts from (a,b) must end at (c,d)
-/
def pathsFromTo (a b : LatticePoint) : Set LatticePath :=
  { path | path.isPathFromTo a b }
def numPaths (a b : LatticePoint) : ℕ :=
  if a.1 ≤ b.1 ∧ a.2 ≤ b.2 then
    ((b.1 - a.1) + (b.2 - a.2)).toNat.choose (b.1 - a.1).toNat
  else 0
/-!
### Bijection between paths and subsets

The key to proving the counting formula is establishing a bijection between:
- Lattice paths from (0,0) to (m,n) with m east steps and n north steps
- Subsets S ⊆ {0, 1, ..., m+n-1} of cardinality m

The bijection: A path corresponds to choosing which m positions (out of m+n total steps)
are east steps. The subset S records exactly those positions.
-/


/-- Given a subset S ⊆ Fin(m+n), construct the path where east steps are at positions in S. -/
def pathFromSubset (m n : ℕ) (S : Finset (Fin (m + n))) : LatticePath :=
  (List.finRange (m + n)).map (fun i => if i ∈ S then LatticeStep.east else LatticeStep.north)

/-- The set of paths with exactly m east steps (as a Finset). -/
def pathsWithMEastSteps (m n : ℕ) : Finset LatticePath :=
  (Finset.univ.filter (fun S : Finset (Fin (m + n)) => S.card = m)).image (pathFromSubset m n)

/-- Given a path, extract the subset of positions where east steps occur. -/
def subsetFromPath (m n : ℕ) (path : LatticePath) (hlen : path.length = m + n) :
    Finset (Fin (m + n)) :=
  Finset.univ.filter (fun i => path[i.val]'(by omega) = LatticeStep.east)
/-!
## Path Tuples, Nipats, and Ipats (Definition def.lgv.path-tups)

A k-vertex is a k-tuple of lattice points.
A path tuple from k-vertex A to k-vertex B is a k-tuple of paths where
the i-th path goes from A_i to B_i.

A path tuple is non-intersecting (nipat) if no two paths share a vertex.
A path tuple is intersecting (ipat) if some two paths share a vertex.
-/


/-- A k-vertex is a k-tuple of lattice points.
    Label: def.lgv.path-tups (a) -/
abbrev kVertex (k : ℕ) := Fin k → LatticePoint

/-- Permute a k-vertex by a permutation σ.
    Label: def.lgv.path-tups (b) -/
def kVertex.permute {k : ℕ} (v : kVertex k) (σ : Equiv.Perm (Fin k)) : kVertex k :=
  fun i => v (σ i)

/-- A path tuple from k-vertex A to k-vertex B.
    Label: def.lgv.path-tups (c) -/
structure PathTuple (k : ℕ) (A B : kVertex k) where
  /-- The i-th path in the tuple -/
  paths : Fin k → LatticePath
  /-- Each path goes from A_i to B_i -/
  valid : ∀ i, (paths i).isPathFromTo (A i) (B i)

/-- The set of vertices visited by a path in a path tuple. -/
def PathTuple.verticesOf {k : ℕ} {A B : kVertex k} (pt : PathTuple k A B)
    (i : Fin k) : Set LatticePoint :=
  { p | p ∈ (pt.paths i).vertices (A i) }

/-- A path tuple is non-intersecting (nipat) if no two distinct paths share a vertex.
    Label: def.lgv.path-tups (d) -/
def PathTuple.isNonIntersecting {k : ℕ} {A B : kVertex k} (pt : PathTuple k A B) : Prop :=
  ∀ i j, i ≠ j → Disjoint (pt.verticesOf i) (pt.verticesOf j)

/-- A path tuple is intersecting (ipat) if it is not non-intersecting.
    Label: def.lgv.path-tups (e) -/
def PathTuple.isIntersecting {k : ℕ} {A B : kVertex k} (pt : PathTuple k A B) : Prop :=
  ¬pt.isNonIntersecting

/-- The set of all path tuples from A to B. -/
def pathTuplesFromTo {k : ℕ} (A B : kVertex k) : Set (PathTuple k A B) :=
  Set.univ

/-- The set of all non-intersecting path tuples (nipats) from A to B. -/
def nipatsFromTo {k : ℕ} (A B : kVertex k) : Set (PathTuple k A B) :=
  { pt | pt.isNonIntersecting }

/-- The set of all intersecting path tuples (ipats) from A to B. -/
def ipatsFromTo {k : ℕ} (A B : kVertex k) : Set (PathTuple k A B) :=
  { pt | pt.isIntersecting }
/-!
## General k Involution Infrastructure

The sign-reversing involution for general k path tuples works as follows:
Given an intersecting path tuple (ipat), we:
1. Find the smallest path index i that contains a "crowded" vertex (shared with another path)
2. Find the first crowded vertex v on path i (by position in the path)
3. Find the largest path index j that contains v (j > i since v is crowded)
4. Exchange the tails of paths i and j at v
5. Compose σ with the transposition (i j) to flip the sign

This maps (σ, ipat) to (σ * swap(i,j), ipat') where:
- sign(σ * swap(i,j)) = -sign(σ) (transposition flips sign)
- ipat' is still intersecting (v is still a crowded point)
- The involution is its own inverse (applying twice returns the original)

Since every ipat has at least one crowded point, the involution has no fixed points.
-/


/-- A vertex is crowded in a path tuple if it appears in at least two paths -/
def PathTuple.isCrowded {k : ℕ} {A B : kVertex k} (pt : PathTuple k A B) (v : LatticePoint) : Prop :=
  ∃ i j : Fin k, i ≠ j ∧ v ∈ pt.verticesOf i ∧ v ∈ pt.verticesOf j

/-- An intersecting path tuple has at least one crowded vertex -/
theorem PathTuple.isIntersecting_iff_exists_crowded {k : ℕ} {A B : kVertex k} (pt : PathTuple k A B) :
    pt.isIntersecting ↔ ∃ v, pt.isCrowded v := by
  unfold isIntersecting isNonIntersecting isCrowded
  push Not
  constructor
  · intro ⟨i, j, hij, hnotdisj⟩
    rw [Set.not_disjoint_iff] at hnotdisj
    obtain ⟨v, hvi, hvj⟩ := hnotdisj
    exact ⟨v, i, j, hij, hvi, hvj⟩
  · intro ⟨v, i, j, hij, hvi, hvj⟩
    use i, j, hij
    rw [Set.not_disjoint_iff]
    exact ⟨v, hvi, hvj⟩

/-- The set of path indices that have a crowded vertex (shared with another path) -/
noncomputable def PathTuple.crowdedPathIndices {k : ℕ} {A B : kVertex k} (pt : PathTuple k A B) : Finset (Fin k) :=
  @Finset.filter _ (fun i => ∃ j : Fin k, i ≠ j ∧ ¬Disjoint (pt.verticesOf i) (pt.verticesOf j)) 
    (Classical.decPred _) Finset.univ


/-- An intersecting path tuple has nonempty crowdedPathIndices -/
theorem PathTuple.isIntersecting_iff_crowdedPathIndices_nonempty {k : ℕ} {A B : kVertex k}
    (pt : PathTuple k A B) :
    pt.isIntersecting ↔ pt.crowdedPathIndices.Nonempty := by
  rw [isIntersecting_iff_exists_crowded]
  constructor
  · intro ⟨v, i, j, hij, hvi, hvj⟩
    use i
    simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨j, hij, by rw [Set.not_disjoint_iff]; exact ⟨v, hvi, hvj⟩⟩
  · intro ⟨i, hi⟩
    simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨j, hij, hnotdisj⟩ := hi
    rw [Set.not_disjoint_iff] at hnotdisj
    obtain ⟨v, hvi, hvj⟩ := hnotdisj
    exact ⟨v, i, j, hij, hvi, hvj⟩
noncomputable def PathTuple.minCrowdedPathIndex {k : ℕ} {A B : kVertex k} 
    (pt : PathTuple k A B) (hip : pt.isIntersecting) : Fin k :=
  (pt.crowdedPathIndices.min' (pt.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip))

/-- The crowded vertices on a specific path: vertices that appear in multiple paths -/
def PathTuple.crowdedVerticesOnPath {k : ℕ} {A B : kVertex k} 
    (pt : PathTuple k A B) (i : Fin k) : Set LatticePoint :=
  { v | v ∈ pt.verticesOf i ∧ ∃ j : Fin k, i ≠ j ∧ v ∈ pt.verticesOf j }

/-- A path tuple with permutation: pairs (σ, pt) where pt is a path tuple from A to σ(B) -/
def pathTupleWithPerm {k : ℕ} (A B : kVertex k) : Type :=
  (σ : Equiv.Perm (Fin k)) × PathTuple k A (B.permute σ)

/-- The sign of a path tuple with permutation -/
def signOfPathTupleWithPerm {k : ℕ} {A B : kVertex k} (sp : pathTupleWithPerm A B) : ℤ :=
  Equiv.Perm.sign sp.1

/-- The set of all ipats with permutation -/
def ipatWithPerm {k : ℕ} (A B : kVertex k) : Set (pathTupleWithPerm A B) :=
  { sp | sp.2.isIntersecting }
/-!
## The LGV Lemma for Two Paths (Proposition prop.lgv.2paths.count)

For two 2-vertices (A, A') and (B, B'):

det | #paths(A→B)   #paths(A→B')  |
    | #paths(A'→B)  #paths(A'→B') |

= #nipats from (A,A') to (B,B') - #nipats from (A,A') to (B',B)

The proof uses a sign-reversing involution on intersecting path tuples
that exchanges the tails of two intersecting paths.
-/


/-- The path count matrix for two source and target points. -/
def pathMatrix2 (A A' B B' : LatticePoint) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![numPaths A B, numPaths A B';
     numPaths A' B, numPaths A' B']

/-- Number of nipats from (A,A') to (B,B').
    Defined as the cardinality of the set of non-intersecting path tuples. -/
noncomputable def numNipats2 (A A' B B' : LatticePoint) : ℕ :=
  let AB : kVertex 2 := ![A, A']
  let BB : kVertex 2 := ![B, B']
  (nipatsFromTo AB BB).ncard

/-- A path tuple from (A,A') to (B,B') or (B',B) with a sign.
    Sign is +1 for (B,B') and -1 for (B',B). -/
structure SignedPathTuple2 (A A' B B' : LatticePoint) where
  /-- The first path -/
  path0 : LatticePath
  /-- The second path -/
  path1 : LatticePath
  /-- Whether this is to (B,B') (true) or (B',B) (false) -/
  toBB' : Bool
  /-- Path 0 goes from A to its destination -/
  valid0 : path0.isPathFromTo A (if toBB' then B else B')
  /-- Path 1 goes from A' to its destination -/
  valid1 : path1.isPathFromTo A' (if toBB' then B' else B)

/-- The sign of a signed path tuple. -/
def SignedPathTuple2.sign {A A' B B' : LatticePoint} (spt : SignedPathTuple2 A A' B B') : ℤ :=
  if spt.toBB' then 1 else -1

/-- Check if a signed path tuple is intersecting (the two paths share a vertex). -/
def SignedPathTuple2.isIntersecting {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B') : Prop :=
  ∃ v, v ∈ spt.path0.vertices A ∧ v ∈ spt.path1.vertices A'

/-- The set of all signed path tuples from (A,A') to (B,B') or (B',B). -/
def signedPathTuples2 (A A' B B' : LatticePoint) : Set (SignedPathTuple2 A A' B B') :=
  Set.univ

/-- The set of intersecting signed path tuples. -/
def signedIpats2 (A A' B B' : LatticePoint) : Set (SignedPathTuple2 A A' B B') :=
  { spt | spt.isIntersecting }

/-- The set of non-intersecting signed path tuples. -/
def signedNipats2 (A A' B B' : LatticePoint) : Set (SignedPathTuple2 A A' B B') :=
  { spt | ¬spt.isIntersecting }
/-! ### Deterministic intersection point selection

The key to proving that the sign-reversing involution is involutive is to use a
deterministic choice of intersection point. We define `firstIntersection` to be
the first intersection point in path0's vertex list (by index). This ensures that
after swapping tails, the same point is still the first intersection.
-/


/-- The index of the first intersection point in path0's vertices.
    This is the smallest index i such that (path0.vertices A)[i] ∈ path1.vertices A'. -/
noncomputable def firstIntersectionIdx {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B') (_h : spt.isIntersecting) : ℕ :=
  let verts0 := spt.path0.vertices A
  let verts1 := spt.path1.vertices A'
  verts0.findIdx (fun v => decide (v ∈ verts1))

/-- The index of the first intersection point is valid (less than the length of path0's vertices). -/
theorem firstIntersectionIdx_lt {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B') (h : spt.isIntersecting) :
    firstIntersectionIdx spt h < (spt.path0.vertices A).length := by
  obtain ⟨v, hv0, hv1⟩ := h
  apply List.findIdx_lt_length_of_exists
  use v, hv0
  simp [hv1]

/-- The first intersection point of two intersecting paths.
    This is the first vertex (by index in path0) that is shared by both paths. -/
noncomputable def firstIntersection {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B') (h : spt.isIntersecting) : LatticePoint :=
  let idx := firstIntersectionIdx spt h
  let verts0 := spt.path0.vertices A
  verts0[idx]'(firstIntersectionIdx_lt spt h)

/-- The first intersection point is in path0's vertices. -/
theorem firstIntersection_mem_path0 {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B') (h : spt.isIntersecting) :
    firstIntersection spt h ∈ spt.path0.vertices A := by
  unfold firstIntersection
  apply List.getElem_mem

/-- The first intersection point is in path1's vertices. -/
theorem firstIntersection_mem_path1 {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B') (h : spt.isIntersecting) :
    firstIntersection spt h ∈ spt.path1.vertices A' := by
  unfold firstIntersection firstIntersectionIdx
  simp only
  have hidx := firstIntersectionIdx_lt spt h
  have hfound := @List.findIdx_getElem _ (fun v => decide (v ∈ spt.path1.vertices A'))
                  (spt.path0.vertices A) hidx
  simp at hfound
  convert hfound


/-- Split a path at a vertex, returning (head, tail) where head ends at v and tail starts at v. -/
noncomputable def splitPathAt (path : LatticePath) (start v : LatticePoint)
    (_hv : v ∈ path.vertices start) : LatticePath × LatticePath :=
  -- Find the index where v occurs
  let verts := path.vertices start
  let idx := verts.findIdx (· == v)
  -- Split the path at that index
  (path.take idx, path.drop idx)
/-! ### Helper lemmas for the involution proof -/


/-- vertices equals scanl result -/
theorem vertices_eq_scanl (path : LatticePath) (start : LatticePoint) :
    path.vertices start = path.scanl (fun p s => s.apply p) start := by
  unfold LatticePath.vertices
  cases path with
  | nil => simp [List.scanl]
  | cons step rest =>
    simp only [List.scanl, List.tail_cons]

/-- scanl[i] = (path.take i).endpoint start -/
theorem scanl_getElem_eq_take_endpoint (path : LatticePath) (start : LatticePoint)
    (i : ℕ) (hi : i < (path.scanl (fun p s => s.apply p) start).length) :
    (path.scanl (fun p s => s.apply p) start)[i] = LatticePath.endpoint (path.take i) start := by
  induction path generalizing start i with
  | nil =>
    simp only [List.scanl_nil, List.length_singleton, Nat.lt_one_iff] at hi
    subst hi
    simp [List.scanl, LatticePath.endpoint]
  | cons step rest ih =>
    simp only [List.scanl_cons, List.length_cons] at hi ⊢
    cases i with
    | zero =>
      simp [LatticePath.endpoint]
    | succ j =>
      simp only [List.getElem_cons_succ, List.take_succ_cons, LatticePath.endpoint, List.foldl_cons]
      have hj : j < (rest.scanl (fun p s => s.apply p) (step.apply start)).length := by
        simp only [List.length_scanl] at hi ⊢
        omega
      exact ih (step.apply start) j hj

/-- vertices[i] = (path.take i).endpoint start -/
theorem vertices_getElem_eq_take_endpoint (path : LatticePath) (start : LatticePoint)
    (i : ℕ) (hi : i < (path.vertices start).length) :
    (path.vertices start)[i] = LatticePath.endpoint (path.take i) start := by
  have heq : path.vertices start = path.scanl (fun p s => s.apply p) start := vertices_eq_scanl path start
  have hi' : i < (path.scanl (fun p s => s.apply p) start).length := by
    rw [← heq]
    exact hi
  simp only [heq]
  exact scanl_getElem_eq_take_endpoint path start i hi'

/-- The head of splitPathAt ends at v -/
theorem splitPathAt_head_endpoint (path : LatticePath) (start v : LatticePoint)
    (hv : v ∈ path.vertices start) :
    let verts := path.vertices start
    let idx := verts.findIdx (· == v)
    LatticePath.endpoint (path.take idx) start = v := by
  simp only
  have hidx : (path.vertices start).findIdx (· == v) < (path.vertices start).length := by
    exact List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have hget : (path.vertices start)[(path.vertices start).findIdx (· == v)] = v := by
    have hfound := @List.findIdx_getElem _ (· == v) (path.vertices start) hidx
    simp at hfound
    exact hfound
  have h := vertices_getElem_eq_take_endpoint path start _ hidx
  rw [hget] at h
  exact h.symm

/-- The sign-reversing involution on intersecting signed path tuples.
    Given an ipat, we:
    1. Find the first intersection point v (deterministically, by index in path0)
    2. Exchange the tails of the two paths at v
    3. Flip the sign (swap toBB')

    This maps ipats to (B,B') ↔ ipats to (B',B).

    Note: We use `firstIntersection` instead of `Classical.choose` to ensure the
    involution is truly involutive. The key property is that after swapping tails,
    the same point v is still the first intersection point. -/
noncomputable def ipatInvolution {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B')
    (h : spt.isIntersecting) : SignedPathTuple2 A A' B B' :=
  -- Get the first intersection point (deterministic choice)
  let v := firstIntersection spt h
  let hv0 := firstIntersection_mem_path0 spt h
  let hv1 := firstIntersection_mem_path1 spt h
  -- Get the indices where v occurs in each path's vertices
  let idx0 := (spt.path0.vertices A).findIdx (· == v)
  let idx1 := (spt.path1.vertices A').findIdx (· == v)
  -- Split both paths at v: (head, tail) where head ends at v and tail starts at v
  let head0 := spt.path0.take idx0
  let tail0 := spt.path0.drop idx0
  let head1 := spt.path1.take idx1
  let tail1 := spt.path1.drop idx1
  -- Create new paths by exchanging tails
  let newPath0 := head0 ++ tail1
  let newPath1 := head1 ++ tail0
  -- The new path tuple has flipped sign
  { path0 := newPath0
    path1 := newPath1
    toBB' := !spt.toBB'
    valid0 := by
      -- newPath0 = head0 ++ tail1 goes A → v → (dest of path1)
      -- where dest of path1 = (if spt.toBB' then B' else B)
      -- and (if !spt.toBB' then B else B') = (if spt.toBB' then B' else B)
      show LatticePath.isPathFromTo newPath0 A (if !spt.toBB' then B else B')
      -- head0 goes A → v (by splitPathAt_head_endpoint)
      have hhead0 : LatticePath.isPathFromTo head0 A v :=
        splitPathAt_head_endpoint spt.path0 A v hv0
      -- path1 goes A' → (if spt.toBB' then B' else B)
      -- so tail1 = path1.drop idx1 goes v → (if spt.toBB' then B' else B)
      have hsplit1 := LatticePath.isPathFromTo_take_drop spt.path1 idx1 A' (if spt.toBB' then B' else B) spt.valid1
      have hhead1_eq_v : LatticePath.endpoint head1 A' = v :=
        splitPathAt_head_endpoint spt.path1 A' v hv1
      simp only at hsplit1
      rw [hhead1_eq_v] at hsplit1
      have htail1 : LatticePath.isPathFromTo tail1 v (if spt.toBB' then B' else B) := hsplit1.2
      -- newPath0 = head0 ++ tail1 goes A → v → (if spt.toBB' then B' else B)
      have hconcat := LatticePath.isPathFromTo_append head0 tail1 A v
        (if spt.toBB' then B' else B) hhead0 htail1
      -- (if !spt.toBB' then B else B') = (if spt.toBB' then B' else B)
      convert hconcat using 1
      cases spt.toBB' <;> rfl
    valid1 := by
      -- newPath1 = head1 ++ tail0 goes A' → v → (dest of path0)
      -- where dest of path0 = (if spt.toBB' then B else B')
      -- and (if !spt.toBB' then B' else B) = (if spt.toBB' then B else B')
      show LatticePath.isPathFromTo newPath1 A' (if !spt.toBB' then B' else B)
      -- head1 goes A' → v (by splitPathAt_head_endpoint)
      have hhead1 : LatticePath.isPathFromTo head1 A' v :=
        splitPathAt_head_endpoint spt.path1 A' v hv1
      -- path0 goes A → (if spt.toBB' then B else B')
      -- so tail0 = path0.drop idx0 goes v → (if spt.toBB' then B else B')
      have hsplit0 := LatticePath.isPathFromTo_take_drop spt.path0 idx0 A (if spt.toBB' then B else B') spt.valid0
      have hhead0_eq_v : LatticePath.endpoint head0 A = v :=
        splitPathAt_head_endpoint spt.path0 A v hv0
      simp only at hsplit0
      rw [hhead0_eq_v] at hsplit0
      have htail0 : LatticePath.isPathFromTo tail0 v (if spt.toBB' then B else B') := hsplit0.2
      -- newPath1 = head1 ++ tail0 goes A' → v → (if spt.toBB' then B else B')
      have hconcat := LatticePath.isPathFromTo_append head1 tail0 A' v
        (if spt.toBB' then B else B') hhead1 htail0
      -- (if !spt.toBB' then B' else B) = (if spt.toBB' then B else B')
      convert hconcat using 1
      cases spt.toBB' <;> rfl
  }
def signedNipats2_true (A A' B B' : LatticePoint) : Set (SignedPathTuple2 A A' B B') :=
  { spt ∈ signedNipats2 A A' B B' | spt.toBB' = true }

/-- Define the subset with toBB' = false -/
def signedNipats2_false (A A' B B' : LatticePoint) : Set (SignedPathTuple2 A A' B B') :=
  { spt ∈ signedNipats2 A A' B B' | spt.toBB' = false }

theorem PathTuple.ext' {k : ℕ} {A B : kVertex k} {pt1 pt2 : PathTuple k A B}
    (h : pt1.paths = pt2.paths) : pt1 = pt2 := by
  cases pt1; cases pt2; simp only at h; subst h; rfl
/-!
## Baby Jordan Curve Theorem (Proposition prop.lgv.jordan-2)

If A' is weakly northwest of A, and B' is weakly northwest of B,
then any path from A to B' must intersect any path from A' to B.

This means:
- x(A') ≤ x(A) and y(A') ≥ y(A)
- x(B') ≤ x(B) and y(B') ≥ y(B)

Under these conditions, #nipats from (A,A') to (B',B) = 0.
-/


/-- Point p is weakly northwest of point q. -/
def isWeaklyNorthwestOf (p q : LatticePoint) : Prop :=
  p.x ≤ q.x ∧ p.y ≥ q.y
/-!
## Log-Concavity of Binomial Coefficients (Corollary cor.lgv.binom-unimod)

As an application of the LGV lemma:
C(n,k)² ≥ C(n,k-1) · C(n,k+1)

This follows by choosing appropriate lattice points and applying
Propositions prop.lgv.2paths.count and prop.lgv.jordan-2.
-/
/-!
## The LGV Lemma for k Paths (Proposition prop.lgv.kpaths.count)

For k-vertices A = (A₁, ..., Aₖ) and B = (B₁, ..., Bₖ):

det(#paths from Aᵢ to Bⱼ)_{i,j} = ∑_{σ ∈ Sₖ} (-1)^σ · #nipats from A to σ(B)

The proof generalizes the k=2 case by using a sign-reversing involution
that picks the first pair of intersecting paths and exchanges their tails.
-/
/-! ### Helper lemmas for the product rule -/

/-- Equivalence between PathTuple and subtype of functions. -/
def PathTuple.equivSubtype {k : ℕ} (A B : kVertex k) :
    PathTuple k A B ≃ { f : Fin k → LatticePath // ∀ i, f i ∈ pathsFromTo (A i) (B i) } where
  toFun pt := ⟨pt.paths, pt.valid⟩
  invFun sf := ⟨sf.val, sf.property⟩
  left_inv pt := by cases pt; rfl
  right_inv sf := by cases sf; rfl

/-- The path count matrix for k source and target vertices. -/
def pathMatrixK {k : ℕ} (A B : kVertex k) : Matrix (Fin k) (Fin k) ℤ :=
  Matrix.of fun i j => numPaths (A i) (B j)

/-- Number of nipats from A to σ(B).
    Defined as the cardinality of the set of non-intersecting path tuples. -/
noncomputable def numNipatsK {k : ℕ} (A B : kVertex k) (σ : Equiv.Perm (Fin k)) : ℕ :=
  (nipatsFromTo A (B.permute σ)).ncard

/-- Number of ipats from A to σ(B).
    Defined as the cardinality of the set of intersecting path tuples. -/
noncomputable def numIpatsK {k : ℕ} (A B : kVertex k) (σ : Equiv.Perm (Fin k)) : ℕ :=
  (ipatsFromTo A (B.permute σ)).ncard
/-!
### Bridge to LGV2.lean

We establish the connection between LGV1's path representation and LGV2's.
The key observation is that both represent the same mathematical objects.

The bridge uses the following chain of equivalences:
1. LGV1.LatticeStep ≃ LGV.LatticeStep' (both are {east, north})
2. LGV1.LatticePath ≃ LGV.LatticePath' (both are lists of steps)
3. LGV1.PathTuple k A B ≃ LGV.LatticePath'Tuple k A B (same structure)
4. LGV.LatticePath'Tuple k A B ≃ LGV.PathTuple integerLattice k A B (via latticePath'TupleEquiv)

The intersection property is preserved at each step, so:
- ipatsFromTo A B ≃ ipatSet integerLattice A B
- numIpatsK A B σ = (ipatFinset ... A (permuteKVertex σ B)).card
-/


/-- Equivalence between `LGV1.LatticeStep` and `LGV.LatticeStep'`.
    
    This is a definitional equivalence: both types have the same structure
    (two constructors `east` and `north`), so the equivalence is trivial.
    The equivalence preserves the `apply` function: `latticeStepEquiv_apply`. -/
def latticeStepEquiv : LatticeStep ≃ LGV.LatticeStep' where
  toFun s := match s with
    | LatticeStep.east => LGV.LatticeStep'.east
    | LatticeStep.north => LGV.LatticeStep'.north
  invFun s := match s with
    | LGV.LatticeStep'.east => LatticeStep.east
    | LGV.LatticeStep'.north => LatticeStep.north
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl

/-- The step equivalence preserves the apply function -/
theorem latticeStepEquiv_apply (s : LatticeStep) (p : LatticePoint) :
    (latticeStepEquiv s).apply p = s.apply p := by
  cases s <;> rfl

/-- Map a LatticePath to a LatticePath' -/
def latticePathToLatticePath' (path : LatticePath) : LGV.LatticePath' :=
  path.map latticeStepEquiv

/-- Map a LatticePath' to a LatticePath -/
def latticePath'ToLatticePath (path : LGV.LatticePath') : LatticePath :=
  path.map latticeStepEquiv.symm

/-- The path mapping preserves endpoints -/
theorem latticePathToLatticePath'_endpoint (path : LatticePath) (start : LatticePoint) :
    LGV.LatticePath'.endpoint (latticePathToLatticePath' path) start = path.endpoint start := by
  induction path generalizing start with
  | nil => rfl
  | cons s rest ih =>
    simp only [latticePathToLatticePath', List.map, LatticePath.endpoint, LGV.LatticePath'.endpoint,
      List.foldl_cons, latticeStepEquiv_apply]
    exact ih (s.apply start)

/-- Convert a PathTuple to a LatticePath'Tuple.
    This is part of the key bridge lemma: numIpatsK equals ipatFinset.card.
    The chain of bijections is:
    - LGV1.PathTuple ≃ LGV.LatticePath'Tuple (via step equivalence)
    - LGV.LatticePath'Tuple ≃ LGV.PathTuple integerLattice (via latticePath'TupleEquiv)
    The intersection property is preserved at each step. -/
def pathTupleToLatticePath'Tuple {k : ℕ} {A B : kVertex k} 
    (pt : PathTuple k A B) : LGV.LatticePath'Tuple k A B where
  paths := fun i => latticePathToLatticePath' (pt.paths i)
  valid := fun i => by
    simp only [latticePathToLatticePath'_endpoint]
    exact pt.valid i

/-- Helper: latticeStepEquiv.symm preserves apply -/
theorem latticeStepEquiv_symm_apply (s : LGV.LatticeStep') (p : LatticePoint) :
    (latticeStepEquiv.symm s).apply p = s.apply p := by
  cases s <;> rfl

/-- Convert a LatticePath'Tuple to a PathTuple -/
def latticePath'TupleToPathTuple {k : ℕ} {A B : kVertex k}
    (pt : LGV.LatticePath'Tuple k A B) : PathTuple k A B where
  paths := fun i => latticePath'ToLatticePath (pt.paths i)
  valid := fun i => by
    simp only [LatticePath.isPathFromTo]
    have h := pt.valid i
    simp only [latticePath'ToLatticePath, LatticePath.endpoint, LGV.LatticePath'.endpoint] at h ⊢
    -- Show that mapping through latticeStepEquiv.symm preserves the endpoint
    have key : ∀ (path : LGV.LatticePath') (start : LatticePoint),
        List.foldl (fun p s => s.apply p) start (path.map latticeStepEquiv.symm) = 
        List.foldl (fun p s => s.apply p) start path := by
      intro path start
      induction path generalizing start with
      | nil => rfl
      | cons s rest ih =>
        simp only [List.map_cons, List.foldl_cons]
        rw [latticeStepEquiv_symm_apply]
        exact ih (s.apply start)
    rw [key]
    exact h

/-- The two conversions are inverses -/
theorem pathTuple_latticePath'Tuple_left_inv {k : ℕ} {A B : kVertex k}
    (pt : PathTuple k A B) : latticePath'TupleToPathTuple (pathTupleToLatticePath'Tuple pt) = pt := by
  cases pt
  apply PathTuple.ext'
  funext i
  simp [latticePath'TupleToPathTuple, pathTupleToLatticePath'Tuple,
    latticePath'ToLatticePath, latticePathToLatticePath', List.map_map, Equiv.symm_apply_apply]

theorem pathTuple_latticePath'Tuple_right_inv {k : ℕ} {A B : kVertex k}
    (pt : LGV.LatticePath'Tuple k A B) : pathTupleToLatticePath'Tuple (latticePath'TupleToPathTuple pt) = pt := by
  apply LGV.LatticePath'Tuple.ext
  intro i
  unfold pathTupleToLatticePath'Tuple latticePath'TupleToPathTuple
         latticePathToLatticePath' latticePath'ToLatticePath
  simp only [List.map_map]
  conv_lhs => rw [show (latticeStepEquiv ∘ latticeStepEquiv.symm) = id from funext (fun _ => Equiv.apply_symm_apply _ _)]
  simp only [List.map_id]

/-- Equivalence between LGV1.PathTuple and LGV.LatticePath'Tuple -/
private noncomputable def pathTupleEquivLatticePath'Tuple {k : ℕ} (A B : kVertex k) :
    PathTuple k A B ≃ LGV.LatticePath'Tuple k A B where
  toFun := pathTupleToLatticePath'Tuple
  invFun := latticePath'TupleToPathTuple
  left_inv := pathTuple_latticePath'Tuple_left_inv
  right_inv := pathTuple_latticePath'Tuple_right_inv

/-- Full equivalence between LGV1.PathTuple and LGV.PathTuple integerLattice -/
noncomputable def pathTupleEquivLGVPathTuple {k : ℕ} (A B : kVertex k) :
    PathTuple k A B ≃ LGV.PathTuple LGV.integerLattice k A B :=
  (pathTupleEquivLatticePath'Tuple A B).trans (LGV.latticePath'TupleEquiv A B)
/-!
## Sign-Reversing Involution (Proof Technique)

The proofs of the LGV lemmas use a sign-reversing involution on intersecting
path tuples. Given an ipat, we:

1. Find the first intersection point v (first crowded point on the path with smallest index)
2. Let i be the smallest index of a path containing v
3. Let j be the largest index of a path containing v (j > i since v is crowded)
4. Exchange the tails (parts after v) of paths pᵢ and pⱼ
5. Compose σ with the transposition (i j)

This involution:
- Maps ipats to ipats
- Reverses sign (since composing with a transposition changes parity)
- Has no fixed points
- Is its own inverse (applying twice returns the original)

By Lemma lem.sign.cancel2, the sum over ipats cancels, leaving only nipats.
-/


-- Note: The deterministic `firstIntersection` and `firstIntersectionIdx` are defined earlier
-- in this file (see `firstIntersectionIdx` and `firstIntersection`). They provide a
-- deterministic choice of intersection point that is essential for proving ipatInvolution_involutive.

end LGV1

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import sympy.matrices.determinants.LGV2
import Def.Combinatorics.Young.OmegaInvolution.Part2
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Def.Combinatorics.Young.LittlewoodRichardson.Part17
import Lemma.Matrix.LGV2
import Lemma.Partition.NPartition
import Instance.Combinatorics.Young.PieriJacobiTrudi.Part17
open Finset BigOperators Matrix MvPolynomial

/-!
# The Pieri Rules and Jacobi-Trudi Identities

This file formalizes the Pieri rules for multiplying Schur polynomials by complete
homogeneous or elementary symmetric polynomials, and the Jacobi-Trudi identities
expressing skew Schur polynomials as determinants.

## Main definitions

* `NPartition`: An N-partition is a weakly decreasing N-tuple of nonnegative integers
* `NPartition.IsTranspose`: Predicate asserting that two partitions are transposes
* `SkewPartition`: A skew partition λ/μ is a pair of partitions with μ ⊆ λ
* `SkewPartition.isHorizontalStrip`: A skew partition is a horizontal strip if no two
  boxes in Y(λ/μ) lie in the same column
* `SkewPartition.isVerticalStrip`: A skew partition is a vertical strip if no two
  boxes in Y(λ/μ) lie in the same row
* `SkewPartition.isHorizontalNStrip`: A horizontal n-strip has exactly n boxes
* `SkewPartition.isVerticalNStrip`: A vertical n-strip has exactly n boxes
* `isHorizontalStripFun`: Canonical unbundled horizontal strip predicate with `(lam, mu)` order
* `isVerticalStripFun`: Canonical unbundled vertical strip predicate with `(lam, mu)` order
* `SSYT`: A semistandard Young tableau of shape λ
* `SkewSSYT`: A semistandard Young tableau of skew shape λ/μ
* `LatticePath`: A lattice path in ℤ² using north and east steps
* `Nipat`: A non-intersecting path tuple (for LGV lemma connection)

## Main results

* `pieri_horizontal`: h_n · s_μ = ∑_{λ/μ is horizontal n-strip} s_λ (Theorem thm.sf.pieri(a))
* `pieri_vertical`: e_n · s_μ = ∑_{λ/μ is vertical n-strip} s_λ (Theorem thm.sf.pieri(b))
* `horizontalStrip_iff_entries`: Characterization of horizontal strips via partition entries
    (Proposition prop.sf.strips.entries(a))
* `verticalStrip_iff_entries`: Characterization of vertical strips via partition entries
    (Proposition prop.sf.strips.entries(b))
* `jacobiTrudi_h`: s_{λ/μ} = det(h_{λᵢ - μⱼ - i + j}) (Theorem thm.sf.jt-h)
* `jacobiTrudi_e`: s_{λ/μ} = det(e_{λᵢᵗ - μⱼᵗ - i + j}) (Theorem thm.sf.jt-e)

## References

* Source: AlgebraicCombinatorics/tex/SymmetricFunctions/PieriJacobiTrudi.tex
* [Stanley, *Enumerative Combinatorics, Vol. 2*][Stanley-EC2]
* [Grinberg-Reiner, *Hopf algebras in combinatorics*][GriRei]

## Implementation notes

We work with N-partitions as length-N lists of weakly decreasing nonnegative integers.
Schur polynomials are defined via semistandard Young tableaux (SSYT).
The Jacobi-Trudi identities are proved using the Lindström-Gessel-Viennot lemma
(see AlgebraicCombinatorics/Determinants/LGV2.lean).

For h_n and e_n with negative n, we use the convention h_n = 0 and e_n = 0.

Note: In the source, M is the length of the partition tuples (for Jacobi-Trudi),
while N is the number of variables (entries in tableaux come from [N]).
We use a single parameter N for simplicity in this formalization.

### Strip Definition Conventions

There are three representations for horizontal/vertical strip predicates:

1. **Bundled (`SkewPartition.isHorizontalStrip`)**: Takes a `SkewPartition N` directly.
   Use when working with bundled skew partitions.

2. **Unbundled canonical (`isHorizontalStripFun`)**: Takes `(lam mu : Fin N → ℕ)` with
   argument order matching the mathematical notation λ/μ. **Preferred for new code.**

See `SkewPartition.isHorizontalStrip_iff_isHorizontalStripFun` for the equivalence lemma.
-/


namespace SymmetricFunctions

variable {N : ℕ} {R : Type*} [CommRing R]

/-- The finite set of all nipats for given partitions λ/μ. -/
noncomputable def nipatFinset' (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    Finset (Nipat lam mu hlam hmu hcontained) :=
  Finset.univ

/-!
### LGV Infrastructure for Jacobi-Trudi

The proof of `det_jacobiTrudiMatrixH_eq_nipatSum` requires bridging this file's
`LatticePath` and `Nipat` types with the LGV infrastructure in LGV2.lean.

We define:
1. Source vertices A_i = (μ_i - i, 1) and target vertices B_j = (λ_j - j, N) in ℤ²
2. An arc weight function that assigns X_j to east-steps at height j
3. Helper lemmas connecting the path weight sum to h_n

The key insight is that:
- The Jacobi-Trudi matrix entry (i, j) = h_{λᵢ - μⱼ - i + j}
- This equals the sum of path weights from A_j to B_i
- By LGV nonpermutable, det = sum over non-intersecting path tuples
- Non-intersecting path tuples correspond exactly to our Nipat type
-/


/-- The source k-vertex for the Jacobi-Trudi LGV setup: A_i = (μ_i - i, 1).
    The y-coordinate 1 represents the starting height in the lattice. -/
def jacobiTrudiSourceVertex (mu : Fin N → ℕ) : LGV.kVertex (ℤ × ℤ) N :=
  fun i => (jacobiTrudiSourceX mu i, 1)

/-- The target k-vertex for the Jacobi-Trudi LGV setup: B_j = (λ_j - j, N).
    The y-coordinate N represents the ending height in the lattice. -/
def jacobiTrudiTargetVertex (lam : Fin N → ℕ) : LGV.kVertex (ℤ × ℤ) N :=
  fun j => (jacobiTrudiTargetX lam j, N)

/-- The arc weight function for the Jacobi-Trudi proof.
    East-steps at height j (where 1 ≤ j ≤ N) are weighted by X_{j-1}.
    North-steps are weighted by 1.

    Note: The lattice uses y-coordinates 1 to N, but Fin N uses 0 to N-1.
    An east-step at y-coordinate y gets weight X_{y-1} when 1 ≤ y ≤ N. -/
noncomputable def jacobiTrudiArcWeight :
    LGV.ArcWeight LGV.integerLattice (MvPolynomial (Fin N) R) :=
  fun u v _ =>
    -- An arc from u to v is either an east-step (x increases) or north-step (y increases)
    if v.1 = u.1 + 1 ∧ v.2 = u.2 then
      -- East-step at height u.2: weight is X_{u.2 - 1} if 1 ≤ u.2 ≤ N, else 1
      if h : 1 ≤ u.2 ∧ u.2 ≤ N then
        MvPolynomial.X ⟨(u.2 - 1).toNat, by omega⟩
      else 1
    else
      -- North-step: weight is 1
      1

/-- Extract y-coordinates at east-step positions from a path vertex list.
    For a path from (a, 1) to (c, N), this gives the sequence of y-coordinates
    where east-steps occur. The sequence is weakly increasing and has length (c - a).

    This is a helper function for constructing the bijection between LGV paths and Sym. -/
def extractEastStepYCoords (vertices : List (ℤ × ℤ)) : List ℤ :=
  match vertices with
  | [] => []
  | [_] => []
  | u :: v :: rest =>
    if v.1 = u.1 + 1 then  -- east-step (x increases by 1)
      u.2 :: extractEastStepYCoords (v :: rest)
    else  -- north-step (y increases by 1)
      extractEastStepYCoords (v :: rest)

/-!
## LGV-Nipat Bijection Infrastructure

The following lemmas establish the connection between LGV's `PathTuple.isNonIntersecting`
and our `Nipat.colStrictPaths`. This is needed for step 4 of the Jacobi-Trudi proof.

The key insight is that for lattice paths from (μᵢ - i, 1) to (λᵢ - i, N):
- Two paths intersect (share a vertex) iff they share a point (x, y) for some x, y
- In the integer lattice, paths can only go north or east
- If path i and path j (with i < j) share a vertex, then at some column c,
  they have the same height
- This violates column-strictness (which requires path j to be strictly higher
  than path i at the same column)

Conversely, column-strictness implies non-intersection.

### Bijection Overview

The bijection between LGV paths and our LatticePath works as follows:

**LGV Path → LatticePath:**
An LGV path from (a, 1) to (c, N) in the integer lattice is a sequence of vertices
where each step is either east (+1 in x) or north (+1 in y). We extract the
y-coordinates at which east-steps occur (converted to Fin N by subtracting 1).

**LatticePath → LGV Path:**
A LatticePath has eastStepHeights : List (Fin N) which is weakly increasing.
We construct the LGV path by starting at (a, 1) and making north-steps until
we reach the first east-step height + 1, then east, then more north-steps, etc.

**Weight Preservation:**
- jacobiTrudiArcWeight assigns X_{y-1} to east-steps at height y (for 1 ≤ y ≤ N)
- North-steps are assigned weight 1
- LatticePath.weight = ∏ h ∈ eastStepHeights, X_h
- These match since the bijection maps y-coordinate y to height h = y - 1

**Non-intersection ↔ Column-strictness:**
For paths from sources A_i = (μ_i - i, 1) to targets B_i = (λ_i - i, N):
- Two LGV paths intersect iff they share a vertex (x, y)
- At any x-coordinate, path i has a well-defined y-coordinate (height)
- If paths i < j share vertex (x, y), then at column (x - (μ_i - i)) in path i
  and column (x - (μ_j - j)) in path j, both paths have height y
- Since μ_i - i > μ_j - j (by sorting), the column indices satisfy:
  col_i = x - μ_i + i and col_j = x - μ_j + j
  If μ_i + col_i = μ_j + col_j (same tableau column), then col_i = col_j + (μ_j - μ_i)
- Column-strictness requires height_i < height_j at same tableau column
- Intersection would give height_i = height_j = y, violating column-strictness
-/


/-- Extract the y-coordinates of east-steps from an LGV path vertex list.
    For a path from (a, 1) to (c, N), this returns the y-coordinates at which
    each east-step occurs. -/
def lgvPathEastStepYCoords (vertices : List (ℤ × ℤ)) : List ℤ :=
  match vertices with
  | [] => []
  | [_] => []
  | v₀ :: v₁ :: rest =>
    -- Check if v₀ → v₁ is an east-step (x increases by 1, y stays same)
    if v₁.1 = v₀.1 + 1 ∧ v₁.2 = v₀.2 then
      v₀.2 :: lgvPathEastStepYCoords (v₁ :: rest)
    else
      lgvPathEastStepYCoords (v₁ :: rest)

end SymmetricFunctions

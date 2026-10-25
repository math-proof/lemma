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
import Theorem.Combinatorics.Young.PieriJacobiTrudi.Part17
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

/-- Convert an LGV path from (a, 1) to (c, N) to a LatticePath.
    This extracts the east-step heights and converts them to Fin N. -/
noncomputable def lgvPathToLatticePath (a c : ℤ) (p : LGV.SimpleDigraph.Path LGV.integerLattice)
    (hstart : p.start = (a, 1)) (hfinish : p.finish = (c, (N : ℤ))) :
    LatticePath (N := N) a c where
  eastStepHeights :=
    let ycoords := lgvPathEastStepYCoords p.vertices
    let h : ∀ y ∈ ycoords, 1 ≤ y ∧ y ≤ N := by
      intro y hy
      have hbnd := lgvPathEastStepYCoords_bounded p.vertices p.nonempty p.arcs_valid y hy
      simp only [LGV.SimpleDigraph.Path.start, LGV.SimpleDigraph.Path.finish] at hstart hfinish
      rw [hstart, hfinish] at hbnd
      simp at hbnd
      exact hbnd
    lgvYCoordsToFinN ycoords h
  weaklyIncreasing := by
    apply lgvYCoordsToFinN_isChain
    exact lgvPathEastStepYCoords_weaklyIncreasing p.vertices p.arcs_valid
  length_eq := by
    rw [lgvYCoordsToFinN_length]
    rw [lgvPathEastStepYCoords_length_eq_xDisplacement p.vertices p.nonempty p.arcs_valid]
    simp only [LGV.SimpleDigraph.Path.start, LGV.SimpleDigraph.Path.finish] at hstart hfinish
    simp only [hstart, hfinish]

/-!
### Injectivity of lgvPathToLatticePath

The key lemma for the bijection is that `lgvPathToLatticePath` is injective.
This follows from the fact that paths in the integer lattice from the same start
to the same end are uniquely determined by their east-step y-coordinates.
-/
/-!
### LatticePath to LGV Path Bijection: Inverse Direction

We construct the inverse of `lgvPathToLatticePath`, converting a `LatticePath` back to
an LGV `SimpleDigraph.Path`. This completes the bidirectional conversion between the
two lattice path representations.

**Representation equivalence**:
- `LGV.LatticePath` (in LGV1.lean): `List LatticeStep` (sequence of east/north steps)
- `SymmetricFunctions.LatticePath` (here): `eastStepHeights : List (Fin N)` with constraints

The bijection works because:
1. A path from (a, 1) to (c, N) is uniquely determined by its east-step heights
2. East-step heights form a weakly increasing sequence of length (c - a).toNat
3. This is exactly the data in a LatticePath

**Construction algorithm**:
Given eastStepHeights = [h₀, h₁, ...], construct vertices by:
1. Start at (a, 1)
2. For each height hᵢ (which represents y-coordinate hᵢ.val + 1):
   - Go north until y = hᵢ.val + 1
   - Go east
3. Finally go north until y = N
-/


/-- Build vertices from east-step heights using fuel-based recursion.
    This is the core algorithm for constructing an LGV path from a LatticePath.

    Parameters:
    - N: the height bound (y-coordinates range in [1, N])
    - x, y: current position
    - heights: remaining east-step heights to process
    - fuel: recursion fuel (ensures termination)

    The algorithm:
    - If no heights remain, go north until y = N
    - Otherwise, if y < next_height + 1, go north
    - Otherwise (y = next_height + 1), go east and consume the height -/
def buildVerticesAux (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ) : List (ℤ × ℤ) :=
  match fuel with
  | 0 => [(x, y)]
  | fuel' + 1 =>
    match heights with
    | [] =>
      if y < N then (x, y) :: buildVerticesAux N x (y + 1) [] fuel'
      else [(x, y)]
    | h :: rest =>
      let targetY := (h.val : ℤ) + 1
      if y < targetY then
        (x, y) :: buildVerticesAux N x (y + 1) heights fuel'
      else
        (x, y) :: buildVerticesAux N (x + 1) y rest fuel'

/-- Build the vertices of an LGV path from a LatticePath's east-step heights.

    The fuel is set to (c - a).toNat + N, which is an upper bound on the number
    of vertices: (c - a) east-steps + (N - 1) north-steps + 1 endpoint. -/
def buildVertices (a c : ℤ) (N : ℕ) (eastStepHeights : List (Fin N)) : List (ℤ × ℤ) :=
  let maxSteps := (c - a).toNat + N
  buildVerticesAux N a 1 eastStepHeights maxSteps

/-!
### LGV-Nipat Bijection: PathTuple to Nipat Conversion

The following definitions and lemmas establish the conversion from LGV PathTuples
to our Nipat type. This is used to prove `lgv_nipatWeightSum_eq_nipatSum`.
-/

/-- Convert an LGV PathTuple to a tuple of LatticePaths.
    Each path is converted using lgvPathToLatticePath. -/
noncomputable def pathTupleToLatticePaths (lam mu : Fin N → ℕ)
    (pt : LGV.PathTuple LGV.integerLattice N
      (jacobiTrudiSourceVertex mu) (jacobiTrudiTargetVertex lam)) :
    (i : Fin N) → LatticePath (N := N)
      ((mu i : ℤ) - (i.val : ℤ)) ((lam i : ℤ) - (i.val : ℤ)) :=
  fun i => lgvPathToLatticePath
    ((mu i : ℤ) - (i.val : ℤ))
    ((lam i : ℤ) - (i.val : ℤ))
    (pt.paths i)
    (by unfold jacobiTrudiSourceVertex jacobiTrudiSourceX at pt; exact pt.starts i)
    (by unfold jacobiTrudiTargetVertex jacobiTrudiTargetX at pt; exact pt.finishes i)

end SymmetricFunctions

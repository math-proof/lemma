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
import Theorem.Combinatorics.Young.PieriJacobiTrudi.Part8
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

/-!
## Schur Polynomials

We use Mathlib's symmetric polynomial infrastructure and define Schur polynomials
via semistandard Young tableaux (SSYT).
-/


/-- A semistandard Young tableau (SSYT) of shape λ with entries in [N].
    The entries are weakly increasing along rows and strictly increasing down columns.
    Definition def.sf.ssyt.

    **Note:** This is one of two SSYT definitions in this project:
    - **This definition** (`SymmetricFunctions.SSYT`): Uses dependent types
      `entries : (i : Fin N) → (j : Fin (lam.parts i)) → Fin N`. Standalone structure.
      No `[NeZero N]` requirement. Field names: `rowWeak`, `colStrict`.
    - **Alternative definition** (`SchurBasics.SSYT` in `SchurBasics.lean`): Uses
      `entry : Fin N × ℕ → Fin N` with a support condition. Extends `YoungTableau`.
      Requires `[NeZero N]`. Field names: `row_weak`, `col_strict`.

    The equivalence between these definitions is established in `SSYTEquiv.lean` via
    `SSYTEquiv.ssytEquiv`. Use `SSYTEquiv.toSchurBasicsSSYT` and `SSYTEquiv.toSFSSYT`
    to convert between representations.

    **When to use which:**
    - Use this definition when the dependent type ensures bounds checking at compile time,
      or when `[NeZero N]` is not available.
    - Use `SchurBasics.SSYT` when working with cell coordinates `(i, j)` directly, or when
      extending the `YoungTableau` structure is beneficial. -/
structure SSYT (lam : NPartition N) where
  /-- The entries of the tableau -/
  entries : (i : Fin N) → (j : Fin (lam.parts i)) → Fin N
  /-- Entries are weakly increasing along rows -/
  rowWeak : ∀ i : Fin N, ∀ j k : Fin (lam.parts i), j ≤ k →
    entries i j ≤ entries i k
  /-- Entries are strictly increasing down columns -/
  colStrict : ∀ i : Fin N, ∀ hi : i.val + 1 < N, ∀ j : Fin (lam.parts i),
    ∀ hj : j.val < (lam.parts ⟨i.val + 1, hi⟩),
    entries i j < entries ⟨i.val + 1, hi⟩ ⟨j.val, hj⟩

/-- A semistandard Young tableau of skew shape λ/μ with entries in [N].
    Definition def.sf.skew-schur.

    For a skew tableau, the column-strict condition requires that entries
    are strictly increasing down columns, where column j of Y(λ/μ) consists
    of boxes (i, j) with μᵢ < j ≤ λᵢ.

    **Note:** This is one of two SkewSSYT definitions in this project:
    - **This definition** (`SymmetricFunctions.SkewSSYT`): Uses dependent types. Takes
      `s : SkewPartition N` as a single bundled argument. No `[NeZero N]` requirement.
      Field names: `rowWeak`, `colStrict`.
    - **Alternative definition** (`SchurBasics.SkewSSYT` in `SchurBasics.lean`): Uses
      `entry : Fin N × ℕ → Fin N` with a support condition. Extends `SkewYoungTableau`.
      Takes `lam mu : NPartition N` as separate arguments. Requires `[NeZero N]`.
      Field names: `row_weak`, `col_strict`.

    See `SSYTEquiv.lean` for conversions between representations. -/
structure SkewSSYT (s : SkewPartition N) where
  /-- The entries of the tableau, only for boxes in Y(λ/μ).
      Entry (i, k) corresponds to box (i, μᵢ + k + 1) in Y(λ/μ). -/
  entries : (i : Fin N) → (k : Fin (s.outer.parts i - s.inner.parts i)) → Fin N
  /-- Entries are weakly increasing along rows -/
  rowWeak : ∀ i : Fin N, ∀ j k : Fin (s.outer.parts i - s.inner.parts i),
    j ≤ k → entries i j ≤ entries i k
  /-- Entries are strictly increasing down columns.
      If boxes (i, c) and (i', c) are both in Y(λ/μ) with i < i', then
      T(i, c) < T(i', c). Here c = μᵢ + k + 1 for some k.
      The condition checks: for row i and column offset k, if row i+1 also
      contains column μᵢ + k + 1 (i.e., μᵢ + k + 1 > μᵢ₊₁ and μᵢ + k + 1 ≤ λᵢ₊₁),
      then the entry in row i is strictly less than the entry in row i+1. -/
  colStrict : ∀ i : Fin N, ∀ hi : i.val + 1 < N,
    ∀ k : Fin (s.outer.parts i - s.inner.parts i),
    -- The absolute column is μᵢ + k + 1. For this to be in row i+1:
    -- 1. μᵢ + k + 1 > μᵢ₊₁ (column is after the inner partition in row i+1)
    -- 2. μᵢ + k + 1 ≤ λᵢ₊₁ (column is within the outer partition in row i+1)
    ∀ _hcol : s.inner.parts i + k.val + 1 > s.inner.parts ⟨i.val + 1, hi⟩ ∧
             s.inner.parts i + k.val + 1 ≤ s.outer.parts ⟨i.val + 1, hi⟩,
    -- The offset in row i+1 for the same column
    let k' : ℕ := s.inner.parts i + k.val - s.inner.parts ⟨i.val + 1, hi⟩
    ∀ hk' : k' < s.outer.parts ⟨i.val + 1, hi⟩ - s.inner.parts ⟨i.val + 1, hi⟩,
    entries i k < entries ⟨i.val + 1, hi⟩ ⟨k', hk'⟩

end SymmetricFunctions

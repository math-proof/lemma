/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.LGV2.Part29
import Def.Combinatorics.Young.OmegaInvolution.Part2
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Def.Combinatorics.Young.LittlewoodRichardson.Part17
import Lemma.Matrix.LGV2
import Lemma.Partition.NPartition
import Instance.Combinatorics.Young.PieriJacobiTrudi.Part4
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

namespace NPartition

variable {N : ℕ}

/-- The transpose of a partition.
    See Exercise exe.pars.transpose in the source.
    The transpose λᵗ satisfies: (λᵗ)ᵢ = |{j : λⱼ ≥ i+1}| for each i.
    The length of the transpose equals the first (largest) part of λ. -/
noncomputable def transpose (lam : NPartition N) (hN : 0 < N) : NPartition (lam.parts ⟨0, hN⟩) where
  parts := fun i => (Finset.univ.filter fun j : Fin N => i.val + 1 ≤ lam.parts j).card
  weaklyDecreasing := by
    intro i j hij
    apply Finset.card_le_card
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact le_trans (Nat.add_le_add_right hij 1) hr

/-- Predicate asserting that `lamt` is the transpose of `lam`.
    The transpose λᵗ of a partition λ satisfies:
    (λᵗ)ᵢ = |{j : λⱼ ≥ i}| for each i.

    Since we work with fixed-length tuples, this predicate captures
    when two tuples represent transpose partitions (possibly with trailing zeros). -/
def IsTranspose {M : ℕ} (lam : Fin N → ℕ) (lamt : Fin M → ℕ) : Prop :=
  (∀ i : Fin M, lamt i = (Finset.univ.filter fun j : Fin N => i.val + 1 ≤ lam j).card) ∧
  (∀ j : Fin N, lam j = (Finset.univ.filter fun i : Fin M => j.val + 1 ≤ lamt i).card)

/-! ### Transpose Box Equivalence

For Young tableaux, the transpose property gives a key equivalence:
a box (i, j) is in the diagram λ iff box (j, i) is in the transpose λᵗ.
In the counting formulation: j + 1 ≤ λ_i iff i + 1 ≤ λᵗ_j.

This equivalence is fundamental for proving that the transpose preserves
the number of boxes and for the Bender-Knuth bijection. -/
/-! ### Row and Column Partitions

Special partitions consisting of a single row or column, used in the
alternative proof of Pieri rules via Littlewood-Richardson. -/


/-- The row partition (n, 0, 0, ..., 0) with n boxes in the first row.
    This is the partition corresponding to h_n (complete homogeneous symmetric polynomial).
    Requires N > 0 to have at least one row. -/
def rowPartition (N : ℕ) (n : ℕ) (_hN : 0 < N) : NPartition N where
  parts := fun i => if i.val = 0 then n else 0
  weaklyDecreasing := by
    intro i j hij
    by_cases hi : i.val = 0
    · simp only [hi, ↓reduceIte]
      split_ifs <;> omega
    · by_cases hj : j.val = 0
      · omega  -- i > 0 but j = 0 contradicts i ≤ j
      · simp only [hj, ↓reduceIte, hi]; rfl

/-- The column partition (1, 1, ..., 1, 0, ..., 0) with n ones (n boxes in first column).
    This is the partition corresponding to e_n (elementary symmetric polynomial).
    Requires n ≤ N (can't have more rows than N). -/
def colPartition (N : ℕ) (n : ℕ) (_hn : n ≤ N) : NPartition N where
  parts := fun i => if i.val < n then 1 else 0
  weaklyDecreasing := by
    intro i j hij
    by_cases hi : i.val < n
    · split_ifs <;> omega
    · split_ifs <;> omega

end NPartition

/-!
## NPartition Type Equivalence

This section provides an equivalence between the local `SymmetricFunctions.NPartition`
and the shared `_root_.NPartition` definition from `NPartition.lean`.

This enables gradual migration: code can use the local definition while having
access to theorems proved about the shared definition (and vice versa).
-/


section NPartitionEquiv

variable {N : ℕ}

/-- Convert a local `SymmetricFunctions.NPartition` to the shared `_root_.NPartition`. -/
def NPartition.toShared (μ : NPartition N) : _root_.NPartition N :=
  _root_.NPartition.mk' μ.parts μ.weaklyDecreasing

/-- Convert a shared `_root_.NPartition` to the local `SymmetricFunctions.NPartition`. -/
def NPartition.ofShared (μ : _root_.NPartition N) : NPartition N where
  parts := μ.parts
  weaklyDecreasing := μ.weaklyDecreasing

end NPartitionEquiv
end SymmetricFunctions

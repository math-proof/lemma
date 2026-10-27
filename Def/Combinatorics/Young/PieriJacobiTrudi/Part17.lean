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
import Theorem.Combinatorics.Young.PieriJacobiTrudi.Part11
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

/-- The Schur polynomial s_λ defined as the sum over all SSYT of shape λ.
    Definition def.sf.schur. -/
noncomputable def schur (lam : NPartition N) : MvPolynomial (Fin N) R :=
  ∑ T ∈ ssytFinset lam, T.toMonomial

/-! ### The Schur polynomial of the zero partition

For the zero partition (0, 0, ..., 0), all rows have 0 entries, so there is
exactly one SSYT of this shape (the empty tableau). Its monomial is 1. -/


/-- The unique SSYT of shape 0 (the empty tableau).
    Since all rows have 0 entries, the entries function is vacuously defined. -/
def SSYT.unique : SSYT (0 : NPartition N) where
  entries := fun _ j => Fin.elim0 j
  rowWeak := fun _ j => Fin.elim0 j
  colStrict := fun _ _ j => Fin.elim0 j

/-- The skew Schur polynomial s_{λ/μ} defined as the sum over all skew SSYT.
    Definition def.sf.skew-schur. -/
noncomputable def skewSchur (s : SkewPartition N) : MvPolynomial (Fin N) R :=
  ∑ T ∈ skewSSYTFinset s, T.toMonomial

/-- Convert an SSYT to a SkewSSYT when the inner partition is zero.
    This is an identity on entries since lam i - 0 = lam i definitionally. -/
def ssytToSkewSSYT (lam : Fin N → ℕ) (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (T : SSYT ⟨lam, hlam⟩) :
    SkewSSYT ⟨⟨lam, hlam⟩, ⟨fun _ => 0, fun _ _ _ => le_refl 0⟩, fun _ => Nat.zero_le _⟩ where
  entries i k := T.entries i k  -- lam i - 0 = lam i definitionally
  rowWeak i j k hjk := T.rowWeak i j k hjk
  colStrict i hi k hcol hk' := by
    simp only [Nat.zero_add, Nat.sub_zero] at hk' hcol ⊢
    exact T.colStrict i hi k hk'

/-- Convert a SkewSSYT to an SSYT when the inner partition is zero.
    This is the inverse of ssytToSkewSSYT. -/
def skewSSYTToSSYT (lam : Fin N → ℕ) (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (T : SkewSSYT ⟨⟨lam, hlam⟩, ⟨fun _ => 0, fun _ _ _ => le_refl 0⟩, fun _ => Nat.zero_le _⟩) :
    SSYT ⟨lam, hlam⟩ where
  entries i j := T.entries i j  -- lam i - 0 = lam i definitionally
  rowWeak i j k hjk := T.rowWeak i j k hjk
  colStrict i hi j hj := by
    change j.val < lam ⟨i.val + 1, hi⟩ at hj
    have hcol : j.val + 1 > 0 ∧ j.val + 1 ≤ lam ⟨i.val + 1, hi⟩ := by constructor <;> omega
    have hk' : j.val < lam ⟨i.val + 1, hi⟩ := hj
    have h := T.colStrict i hi j (by simp only [Nat.zero_add, Nat.sub_zero]; exact hcol)
      (by simp only [Nat.zero_add, Nat.sub_zero]; exact hk')
    simp only [Nat.zero_add, Nat.sub_zero] at h
    exact h

/-!
## The Pieri Rules

Theorem thm.sf.pieri: The Pieri rules express products h_n · s_μ and e_n · s_μ
as sums of Schur polynomials.
-/
/-!
### Enumeration of Horizontal and Vertical Strip Partitions

For a fixed N-partition μ and size n, we enumerate all N-partitions λ such that
λ/μ is a horizontal (resp. vertical) n-strip. The key observation is that each
λ_i is bounded:
- Lower bound: λ_i ≥ μ_i (containment)
- Upper bound: λ_i ≤ μ_{i-1} for i > 0 (horizontal strip condition)
- Upper bound: λ_0 ≤ μ_0 + n (since |λ| = |μ| + n)

This makes the enumeration finite.
-/


/-- The bound for each λ_i when forming a horizontal strip with μ.
    λ_i must satisfy μ_i ≤ λ_i ≤ bound_i where:
    - For i = 0: bound_0 = μ_0 + n (since |λ| - |μ| = n and all parts are bounded by λ_0)
    - For i > 0: bound_i = μ_{i-1} (horizontal strip condition: μ_{i-1} ≥ λ_i) -/
def horizontalStripUpperBound (mu : NPartition N) (n : ℕ) (i : Fin N) : ℕ :=
  if h : i.val = 0 then mu.parts ⟨0, Nat.pos_of_ne_zero (by omega : N ≠ 0)⟩ + n
  else mu.parts ⟨i.val - 1, by omega⟩

/-- A function from Fin N to ℕ that could potentially form a horizontal n-strip with μ.
    This is the set of all functions bounded by the horizontal strip constraints. -/
def potentialHorizontalStrips (mu : NPartition N) (n : ℕ) : Finset (Fin N → ℕ) :=
  Fintype.piFinset (fun i => Finset.Icc (mu.parts i) (horizontalStripUpperBound mu n i))

/-- Check if a function forms a valid N-partition (weakly decreasing). -/
def isWeaklyDecreasing (f : Fin N → ℕ) : Prop :=
  ∀ i j : Fin N, i ≤ j → f j ≤ f i

end SymmetricFunctions

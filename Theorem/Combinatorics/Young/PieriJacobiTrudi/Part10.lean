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
import Def.Combinatorics.Young.PieriJacobiTrudi.Part12
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

/-- Column-strictness extends to non-adjacent rows.
    If column c appears in rows i and j with i < j, then T(i, c) < T(j, c).

    This is a key lemma for the nipat-SSYT bijection: it shows that the
    column-strict condition for adjacent rows implies strict inequality
    for any two rows that share a column. The proof uses strong induction
    on the row distance j - i, with the base case being adjacent rows
    (directly using `T.colStrict`) and the inductive case going through
    an intermediate row j' = j - 1. -/
theorem SkewSSYT.colStrict_nonadjacent {s : SkewPartition N}
    (T : SkewSSYT s) (i j : Fin N) (hij : i < j)
    (k : Fin (s.outer.parts i - s.inner.parts i))
    (k' : Fin (s.outer.parts j - s.inner.parts j))
    (hcol_eq : s.inner.parts i + k.val = s.inner.parts j + k'.val) :
    T.entries i k < T.entries j k' := by
  -- Use strong induction on j.val - i.val
  obtain ⟨d, hd_eq⟩ : ∃ d, j.val - i.val = d + 1 := ⟨j.val - i.val - 1, by omega⟩
  induction d using Nat.strong_induction_on generalizing i j k k' with
  | _ d ih =>
    by_cases hd : d = 0
    · -- Base case: adjacent rows (j = i + 1)
      have hj_eq : j.val = i.val + 1 := by omega
      have hi_lt : i.val + 1 < N := by omega
      -- Show j = ⟨i.val + 1, hi_lt⟩
      have hj_fin : j = ⟨i.val + 1, hi_lt⟩ := by
        apply Fin.ext
        exact hj_eq
      subst hj_fin
      -- Now we can apply T.colStrict
      have hcol : s.inner.parts i + k.val + 1 > s.inner.parts ⟨i.val + 1, hi_lt⟩ ∧
                  s.inner.parts i + k.val + 1 ≤ s.outer.parts ⟨i.val + 1, hi_lt⟩ := by
        constructor
        · omega
        · have hk'_lt := k'.isLt
          omega
      -- The offset in row i+1 for the same column
      let k''_val := s.inner.parts i + k.val - s.inner.parts ⟨i.val + 1, hi_lt⟩
      have hk''_eq : k''_val = k'.val := by omega
      have hk''_lt : k''_val < s.outer.parts ⟨i.val + 1, hi_lt⟩ - s.inner.parts ⟨i.val + 1, hi_lt⟩ := by
        rw [hk''_eq]
        exact k'.isLt
      have hres := T.colStrict i hi_lt k hcol hk''_lt
      -- Convert types
      convert hres using 2
      apply Fin.ext
      exact hk''_eq.symm
    · -- Inductive case: j.val - i.val > 1
      have hd_gt : d > 0 := by omega
      have hj_gt : j.val > i.val + 1 := by omega
      -- Find intermediate row j' = j.val - 1
      let j' : Fin N := ⟨j.val - 1, by omega⟩
      have hij' : i < j' := by simp only [j', Fin.lt_def]; omega
      have hj'j : j' < j := by simp only [j', Fin.lt_def]; omega
      -- Key facts from partition monotonicity
      have h_inner_j_le_j' : s.inner.parts j ≤ s.inner.parts j' :=
        s.inner.weaklyDecreasing j' j (le_of_lt hj'j)
      have h_outer_j_le_j' : s.outer.parts j ≤ s.outer.parts j' :=
        s.outer.weaklyDecreasing j' j (le_of_lt hj'j)
      -- The column s.inner.parts i + k.val must appear in row j' too
      have hcol_in_j' : s.inner.parts j' < s.inner.parts i + k.val + 1 ∧
                        s.inner.parts i + k.val + 1 ≤ s.outer.parts j' := by
        constructor
        · have h_inner_j'_le_i : s.inner.parts j' ≤ s.inner.parts i :=
            s.inner.weaklyDecreasing i j' (le_of_lt hij')
          omega
        · have hk'_lt := k'.isLt
          omega
      -- Define k'' as the offset in row j' for the same column
      let k''_val := s.inner.parts i + k.val - s.inner.parts j'
      have hk''_lt : k''_val < s.outer.parts j' - s.inner.parts j' := by
        simp only [k''_val]
        have h_inner_j'_le_i : s.inner.parts j' ≤ s.inner.parts i :=
          s.inner.weaklyDecreasing i j' (le_of_lt hij')
        have hk_lt := k.isLt
        have hk'_lt := k'.isLt
        omega
      let k'' : Fin (s.outer.parts j' - s.inner.parts j') := ⟨k''_val, hk''_lt⟩
      have hcol_eq' : s.inner.parts i + k.val = s.inner.parts j' + k''.val := by
        simp only [k'', k''_val]
        have h_inner_j'_le_i : s.inner.parts j' ≤ s.inner.parts i :=
          s.inner.weaklyDecreasing i j' (le_of_lt hij')
        omega
      -- Apply IH for i → j'
      have hdiff' : j'.val - i.val - 1 < d := by simp only [j']; omega
      have hdiff'_eq : j'.val - i.val = (j'.val - i.val - 1) + 1 := by omega
      have h1 : T.entries i k < T.entries j' k'' :=
        ih (j'.val - i.val - 1) hdiff' i j' hij' k k'' hcol_eq' hdiff'_eq
      -- Apply IH for j' → j
      have hcol_eq'' : s.inner.parts j' + k''.val = s.inner.parts j + k'.val := by
        simp only [k'', k''_val]
        have h_inner_j'_le_i : s.inner.parts j' ≤ s.inner.parts i :=
          s.inner.weaklyDecreasing i j' (le_of_lt hij')
        omega
      have hdiff'' : j.val - j'.val - 1 < d := by simp only [j']; omega
      have hdiff''_eq : j.val - j'.val = (j.val - j'.val - 1) + 1 := by simp only [j']; omega
      have h2 : T.entries j' k'' < T.entries j k' :=
        ih (j.val - j'.val - 1) hdiff'' j' j hj'j k'' k' hcol_eq'' hdiff''_eq
      -- Combine by transitivity
      exact lt_trans h1 h2

end SymmetricFunctions

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
import Instance.Combinatorics.Young.PieriJacobiTrudi.Part14
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

/-! ### Note on Horizontal Strips and Semistandard Tableaux

**WARNING:** The statement "horizontal strip + semistandard ⟹ all entries 0" is FALSE.

**Counterexample:** N = 2, λ = (2, 1), μ = (1, 0)
- This is a horizontal strip: μ₀ = 1 ≥ λ₁ = 1 ✓
- Cells: (0, 2) and (1, 1) — in different columns
- Any assignment is semistandard (vacuously, since no two cells share a row or column)
- In particular, T(0, 2) = 1 gives a non-zero entry

**WARNING:** The statement "Yamanouchi w.r.t. row partition ⟹ all entries 0" is also FALSE
without the horizontal strip hypothesis!

**Counterexample:** N = 3, λ = (2, 2, 0), μ = (0, 0, 0), n = 1, ν = (1, 0, 0)
- This is NOT a horizontal strip (both row 0 and row 1 have 2 cells)
- The tableau T with T(0,1) = 0, T(0,2) = 1, T(1,1) = 1, T(1,2) = 2 is semistandard
- At j = 1: ν + contentColGeq T 1 = (1, 0, 0) + (1, 2, 1) = (2, 2, 1), an N-partition ✓
- At j = 2: ν + contentColGeq T 2 = (1, 0, 0) + (0, 1, 1) = (1, 1, 1), an N-partition ✓
- So T is (1, 0, 0)-Yamanouchi, but has positive entries 1 and 2!

The correct characterization requires BOTH being a horizontal strip AND being Yamanouchi
with respect to a row partition.
-/


/-- Convert a Sym to an SSYT of row partition shape.
    The sorted multiset gives a weakly increasing sequence for row 0. -/
def symToRowSSYT (hN : 0 < N) (n : ℕ) (s : Sym (Fin N) n) :
    SSYT (NPartition.rowPartition N n hN) where
  entries i j :=
    -- Row 0 has n boxes, other rows have 0 boxes
    if hi : i.val = 0 then
      -- In row 0, use the sorted multiset
      have hj_lt : j.val < n := by
        have hj := j.isLt
        simp only [NPartition.rowPartition, hi, ↓reduceIte] at hj
        exact hj
      (symToWeaklyIncreasing n s).val ⟨j.val, hj_lt⟩
    else
      -- Other rows are empty, so this is impossible
      (Fin.elim0 (by
        have hj := j.isLt
        simp only [NPartition.rowPartition, hi, ↓reduceIte] at hj
        exact ⟨j.val, hj⟩ : Fin 0))
  rowWeak i j k hjk := by
    simp only
    split_ifs with hi
    · -- Row 0: use weakly increasing property
      exact (symToWeaklyIncreasing n s).property _ _ hjk
    · -- Other rows are empty
      have hj := j.isLt
      simp only [NPartition.rowPartition, hi, ↓reduceIte] at hj
      exact (Nat.not_lt_zero j.val hj).elim
  colStrict i hi j hj := by
    -- Column strictness is vacuous since only row 0 has boxes
    -- Row i+1 has 0 boxes since i.val + 1 ≠ 0
    have hparts : (NPartition.rowPartition N n hN).parts ⟨i.val + 1, hi⟩ = 0 := by
      simp only [NPartition.rowPartition]
      have : (⟨i.val + 1, hi⟩ : Fin N).val ≠ 0 := Nat.succ_ne_zero i.val
      simp only [this, ↓reduceIte]
    rw [hparts] at hj
    exact (Nat.not_lt_zero j.val hj).elim

/-- Convert an SSYT of row partition shape back to a Sym.
    Row 0 entries form a weakly increasing sequence which gives a multiset. -/
def rowSSYTToSym (hN : 0 < N) (n : ℕ) (T : SSYT (NPartition.rowPartition N n hN)) :
    Sym (Fin N) n := by
  -- Row 0 has n boxes
  have hrow0 : (NPartition.rowPartition N n hN).parts ⟨0, hN⟩ = n := by
    simp [NPartition.rowPartition]
  -- Extract entries from row 0
  let entries0 : Fin n → Fin N := fun j => T.entries ⟨0, hN⟩ ⟨j.val, by rw [hrow0]; exact j.isLt⟩
  exact weaklyIncreasingToSym n entries0

/-- Convert a subset of size n to an SSYT of column partition shape.
    The sorted subset gives a strictly increasing sequence for column 0. -/
def finsetToColSSYT (n : ℕ) (hn : n ≤ N) (s : Finset (Fin N)) (hs : s.card = n) :
    SSYT (NPartition.colPartition N n hn) where
  entries i j :=
    if hi : i.val < n then
      (s.sort (· ≤ ·)).get ⟨i.val, by rw [Finset.length_sort, hs]; exact hi⟩
    else
      (Fin.elim0 (by
        have hj := j.isLt
        simp only [NPartition.colPartition, hi, ↓reduceIte] at hj
        exact ⟨j.val, hj⟩ : Fin 0))
  rowWeak i j k _ := by
    simp only
    split_ifs with hi
    · rfl
    · have hj := j.isLt
      simp only [NPartition.colPartition, hi, ↓reduceIte] at hj
      exact (Nat.not_lt_zero j.val hj).elim
  colStrict i hi j hj := by
    simp only
    have hi_lt_n : i.val < n := by
      have hj' := j.isLt
      simp only [NPartition.colPartition] at hj'
      by_cases h : i.val < n
      · exact h
      · simp only [h, ↓reduceIte] at hj'
        exact (Nat.not_lt_zero j.val hj').elim
    have hi1_lt_n : i.val + 1 < n := by
      simp only [NPartition.colPartition] at hj
      by_cases h : i.val + 1 < n
      · exact h
      · simp only [h, ↓reduceIte] at hj
        exact (Nat.not_lt_zero j.val hj).elim
    simp only [hi_lt_n, hi1_lt_n, dite_true]
    have hlen1 : i.val < (s.sort (· ≤ ·)).length := by rw [Finset.length_sort, hs]; omega
    have hlen2 : i.val + 1 < (s.sort (· ≤ ·)).length := by rw [Finset.length_sort, hs]; omega
    have hlt : (⟨i.val, hlen1⟩ : Fin (s.sort (· ≤ ·)).length) < ⟨i.val + 1, hlen2⟩ := by
      simp only [Fin.lt_def]; omega
    convert s.sortedLT_sort hlt

/-- Helper for extracting entry from column SSYT -/
def colSSYTEntry (n : ℕ) (hn : n ≤ N) (T : SSYT (NPartition.colPartition N n hn))
    (k : ℕ) (hk : k < n) : Fin N :=
  have hkN : k < N := Nat.lt_of_lt_of_le hk hn
  have h0 : 0 < (NPartition.colPartition N n hn).parts ⟨k, hkN⟩ := by
    simp [NPartition.colPartition, hk]
  T.entries ⟨k, hkN⟩ ⟨0, h0⟩

/-- Inverse bijection: SSYT(colPartition) → Finset -/
def colSSYTToFinset (n : ℕ) (hn : n ≤ N) (T : SSYT (NPartition.colPartition N n hn)) :
    Finset (Fin N) :=
  Finset.univ.image (fun k : Fin n => colSSYTEntry n hn T k.val k.isLt)

/-!
## The Jacobi-Trudi Identities

The Jacobi-Trudi identities express skew Schur polynomials as determinants
of matrices involving h_n or e_n.
-/


/-- Extended h_n: h_n = 0 for n < 0, h_0 = 1.
    This is needed since the Jacobi-Trudi formula may have negative indices. -/
noncomputable def hsymmExt (n : ℤ) : MvPolynomial (Fin N) R :=
  if 0 ≤ n then hsymm (Fin N) R n.toNat else 0

/-- The Jacobi-Trudi matrix for h (first Jacobi-Trudi formula).
    Entry (i,j) is h_{λᵢ - μⱼ - i + j}. -/
noncomputable def jacobiTrudiMatrixH (lam mu : Fin N → ℕ) :
    Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) R) :=
  Matrix.of fun i j =>
    hsymmExt ((lam i : ℤ) - (mu j : ℤ) - (i.val : ℤ) + (j.val : ℤ))

/-!
## LGV Lemma Connection

The proof of the first Jacobi-Trudi formula uses the LGV lemma.
We outline the key constructions here.
-/
/-!
### Source and Target Vertices for Jacobi-Trudi

For the Jacobi-Trudi identity, we define:
- Source vertices: Aᵢ = (μᵢ - i, 1) for i ∈ [N]
- Target vertices: Bⱼ = (λⱼ - j, N) for j ∈ [N]

These vertices satisfy the sorting conditions required by the LGV lemma
(Corollary cor.lgv.kpaths.wt-np):
- x-coordinates are weakly decreasing: x(A₁) ≥ x(A₂) ≥ ... ≥ x(Aₖ)
- y-coordinates are constant (trivially weakly increasing)
-/


/-- The source vertex A_i = (μ_i - i, 1) for the Jacobi-Trudi LGV setup.
    Here 1 represents the "starting height" in the lattice. -/
def jacobiTrudiSourceX (mu : Fin N → ℕ) (i : Fin N) : ℤ :=
  (mu i : ℤ) - (i.val : ℤ)

/-- The target vertex B_j = (λ_j - j, N) for the Jacobi-Trudi LGV setup.
    Here N represents the "ending height" in the lattice. -/
def jacobiTrudiTargetX (lam : Fin N → ℕ) (j : Fin N) : ℤ :=
  (lam j : ℤ) - (j.val : ℤ)

end SymmetricFunctions

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import sympy.matrices.determinants.LGV2
import sympy.combinatorics.symmetric.OmegaInvolution
import sympy.combinatorics.partitions.NPartition
import sympy.combinatorics.symmetric.LittlewoodRichardson
import Lemma.Matrix.LGV2
import Lemma.Partition.NPartition
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


open Finset BigOperators Matrix MvPolynomial

namespace SymmetricFunctions

variable {N : ℕ} {R : Type*} [CommRing R]
/-!
## N-Partitions

An N-partition is a weakly decreasing N-tuple of nonnegative integers.

**DEPRECATION NOTE:** This is a local definition within the `SymmetricFunctions` namespace.
A canonical definition exists at the top level in `NPartition.lean` (see
`AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean`). New code should prefer
the canonical definition. This local definition uses `weaklyDecreasing` as the field name,
while the canonical definition uses `antitone` (which matches Mathlib conventions).
Both are semantically equivalent.

**Migration support:** An equivalence `NPartition.equivShared` is provided below
to convert between the local and shared definitions. This enables gradual migration:
- Use `NPartition.toShared` to convert local → shared
- Use `NPartition.ofShared` to convert shared → local
- Both preserve `parts`, `size`, and the `≤` relation

**Note:** `MonomialSymmetric.lean` and `SchurBasics.lean` have been migrated to use
the canonical definition. This file retains the local definition to avoid large
refactoring of the extensive APIs built on top of it.
-/


/-- An N-partition is a list of length N with weakly decreasing nonnegative entries.
    This corresponds to Definition def.sf.N-par in the source.

    **Note:** This is `SymmetricFunctions.NPartition`, a local definition.
    A canonical top-level `NPartition` exists in `NPartition.lean` with the same
    semantics (using `antitone` as the field name instead of `weaklyDecreasing`).
    See the section docstring for details. -/
structure NPartition (N : ℕ) where
  /-- The parts of the partition -/
  parts : Fin N → ℕ
  /-- The parts are weakly decreasing -/
  weaklyDecreasing : ∀ i j : Fin N, i ≤ j → parts j ≤ parts i

namespace NPartition

variable {N : ℕ}

/-- Two N-partitions are equal if their parts are equal. -/
@[ext]
theorem ext {lam mu : NPartition N} (h : lam.parts = mu.parts) : lam = mu := by
  cases lam; cases mu; simp_all

/-- Decidable equality for N-partitions. -/
instance instDecidableEq : DecidableEq (NPartition N) := fun lam mu =>
  decidable_of_iff (lam.parts = mu.parts) ⟨ext, fun h => h ▸ rfl⟩

/-- The zero partition (0, 0, ..., 0) -/
def zero (N : ℕ) : NPartition N where
  parts := fun _ => 0
  weaklyDecreasing := fun _ _ _ => le_refl 0

instance : Zero (NPartition N) := ⟨zero N⟩

/-- The size (sum of parts) of an N-partition -/
def size (lam : NPartition N) : ℕ := ∑ i, lam.parts i

/-- Containment of partitions: μ ⊆ λ means μᵢ ≤ λᵢ for all i -/
def partLE (mu lam : NPartition N) : Prop := ∀ i, mu.parts i ≤ lam.parts i

instance : LE (NPartition N) := ⟨partLE⟩

theorem le_def (mu lam : NPartition N) : mu ≤ lam ↔ ∀ i, mu.parts i ≤ lam.parts i := Iff.rfl

/-- Decidable instance for partition containment. -/
instance instDecidableLE : DecidableRel (fun (a b : NPartition N) => a ≤ b) :=
  fun _ _ => Fintype.decidableForallFintype

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

/-- Converting to shared and back is the identity. -/
@[simp]
theorem NPartition.ofShared_toShared (μ : NPartition N) :
    NPartition.ofShared (NPartition.toShared μ) = μ := by
  ext; rfl

/-- Converting from shared and back is the identity. -/
@[simp]
theorem NPartition.toShared_ofShared (μ : _root_.NPartition N) :
    NPartition.toShared (NPartition.ofShared μ) = μ := by
  ext; rfl

/-- The equivalence between local and shared NPartition types. -/
def NPartition.equivShared : NPartition N ≃ _root_.NPartition N where
  toFun := NPartition.toShared
  invFun := NPartition.ofShared
  left_inv := NPartition.ofShared_toShared
  right_inv := NPartition.toShared_ofShared

end NPartitionEquiv
/-!
## Transpose Bridge Lemmas

These lemmas connect the local `SymmetricFunctions.NPartition.transpose` with the
canonical `_root_.NPartition.transpose` via the `toShared`/`ofShared` equivalence.

Both definitions compute the same thing: (λᵗ)ᵢ = |{j : λⱼ ≥ i+1}| for each i.
The bridge lemmas make this equivalence explicit, enabling code using the local
definition to interoperate with theorems proved about the canonical definition.
-/


section TransposeBridge

variable {N : ℕ}

end TransposeBridge
/-!
## Helper Lemmas for Sym-SSYT Bijection

These lemmas establish the connection between `Sym (Fin N) n` (multisets of size n)
and weakly increasing sequences, which is key for proving that h_n equals the
Schur polynomial of the row partition.
-/


section SymSSYTHelpers

variable {N : ℕ}

/-- A sorted multiset gives a weakly increasing sequence.
    This is because `Multiset.sort` produces a sorted list. -/
theorem sorted_weakly_increasing {α : Type*} [LinearOrder α] (m : Multiset α) :
    ∀ i j : Fin (m.sort (· ≤ ·)).length, i ≤ j →
      (m.sort (· ≤ ·)).get i ≤ (m.sort (· ≤ ·)).get j := by
  intro i j hij
  apply List.Pairwise.rel_get_of_le
  · exact Multiset.pairwise_sort m (· ≤ ·)
  · exact hij

/-- Convert a Sym to a weakly increasing function.
    The sorted list of a multiset gives a canonical weakly increasing sequence. -/
def symToWeaklyIncreasing (n : ℕ) (s : Sym (Fin N) n) :
    { f : Fin n → Fin N // ∀ i j, i ≤ j → f i ≤ f j } := by
  have hlen : (s.1.sort (· ≤ ·)).length = n := by rw [Multiset.length_sort]; exact s.2
  refine ⟨fun i => (s.1.sort (· ≤ ·)).get ⟨i.val, by rw [hlen]; exact i.isLt⟩, ?_⟩
  intro i j hij
  apply sorted_weakly_increasing
  exact hij

/-- Convert a weakly increasing function back to a Sym.
    This is the inverse of symToWeaklyIncreasing. -/
def weaklyIncreasingToSym (n : ℕ) (f : Fin n → Fin N) : Sym (Fin N) n :=
  ⟨Multiset.ofList ((List.finRange n).map f), by simp⟩

end SymSSYTHelpers
/-!
## Skew Partitions and Strips

Definition def.sf.strips: A skew partition λ/μ is a pair (μ, λ) of N-partitions.
Horizontal and vertical strips are special cases where the skew diagram has
no two boxes in the same column or row, respectively.
-/


/-- A skew partition λ/μ is a pair of N-partitions with μ ⊆ λ.
    Definition def.sf.strips(a). -/
structure SkewPartition (N : ℕ) where
  /-- The outer partition λ -/
  outer : NPartition N
  /-- The inner partition μ -/
  inner : NPartition N
  /-- The containment condition μ ⊆ λ -/
  contained : inner ≤ outer

namespace SkewPartition

variable {N : ℕ}

/-- The size of a skew partition |Y(λ/μ)| = |λ| - |μ| -/
def size (s : SkewPartition N) : ℕ := s.outer.size - s.inner.size

/-- A skew partition λ/μ is a horizontal strip if no two boxes of Y(λ/μ)
    lie in the same column.
    Definition def.sf.strips(b).

    **Bundled definition:** This is the preferred version when working with `SkewPartition N`.

    **Related definitions:**
    - `isHorizontalStripFun`: Canonical unbundled version with `(lam, mu)` argument order

    **Equivalence:** `s.isHorizontalStrip ↔ isHorizontalStripFun s.outer.parts s.inner.parts`
    (see `SkewPartition.isHorizontalStrip_iff_isHorizontalStripFun`) -/
def isHorizontalStrip (s : SkewPartition N) : Prop :=
  ∀ i : Fin N, ∀ hi : i.val + 1 < N,
    s.inner.parts i ≥ s.outer.parts ⟨i.val + 1, hi⟩

/-- A skew partition λ/μ is a vertical strip if no two boxes of Y(λ/μ)
    lie in the same row.
    Definition def.sf.strips(c).

    **Bundled definition:** This is the preferred version when working with `SkewPartition N`.

    **Related definitions:**
    - `isVerticalStripFun`: Canonical unbundled version with `(lam, mu)` argument order

    **Equivalence:** `s.isVerticalStrip ↔ isVerticalStripFun s.outer.parts s.inner.parts`
    (see `SkewPartition.isVerticalStrip_iff_isVerticalStripFun`) -/
def isVerticalStrip (s : SkewPartition N) : Prop :=
  ∀ i : Fin N, s.outer.parts i ≤ s.inner.parts i + 1

/-- A skew partition is a horizontal n-strip if it is a horizontal strip
    with |Y(λ/μ)| = n.
    Definition def.sf.strips(d). -/
def isHorizontalNStrip (s : SkewPartition N) (n : ℕ) : Prop :=
  s.isHorizontalStrip ∧ s.size = n

/-- A skew partition is a vertical n-strip if it is a vertical strip
    with |Y(λ/μ)| = n.
    Definition def.sf.strips(e). -/
def isVerticalNStrip (s : SkewPartition N) (n : ℕ) : Prop :=
  s.isVerticalStrip ∧ s.size = n
/-!
### Characterization of Strips

Proposition prop.sf.strips.entries: Horizontal and vertical strips can be
characterized in terms of the entries of the partitions.
-/
/-!
### Decidability and Basic API for Strips

These instances and lemmas make the strip predicates computable and provide
basic API for working with strips.
-/


/-- Decidable instance for `isHorizontalStrip`. -/
instance instDecidableIsHorizontalStrip (s : SkewPartition N) : Decidable s.isHorizontalStrip :=
  Fintype.decidableForallFintype

/-- Decidable instance for `isVerticalStrip`. -/
instance instDecidableIsVerticalStrip (s : SkewPartition N) : Decidable s.isVerticalStrip :=
  Fintype.decidableForallFintype

/-- Decidable instance for `isHorizontalNStrip`. -/
instance instDecidableIsHorizontalNStrip (s : SkewPartition N) (n : ℕ) :
    Decidable (s.isHorizontalNStrip n) :=
  instDecidableAnd

/-- Decidable instance for `isVerticalNStrip`. -/
instance instDecidableIsVerticalNStrip (s : SkewPartition N) (n : ℕ) :
    Decidable (s.isVerticalNStrip n) :=
  instDecidableAnd
/-!
### Examples from the textbook

These examples verify that our definitions match Definition def.sf.strips from
the source (AlgebraicCombinatorics/tex/SymmetricFunctions/PieriJacobiTrudi.tex).
-/


section Examples

/-- Example (a) from the textbook: λ = (8,7,4,3), μ = (7,4,4,1).
    This is a horizontal 6-strip but NOT a vertical strip. -/
def exampleA_outer : NPartition 4 where
  parts := ![8, 7, 4, 3]
  weaklyDecreasing := by decide

def exampleA_inner : NPartition 4 where
  parts := ![7, 4, 4, 1]
  weaklyDecreasing := by decide

def exampleA : SkewPartition 4 where
  outer := exampleA_outer
  inner := exampleA_inner
  contained := by decide

-- This is a horizontal strip
example : exampleA.isHorizontalStrip := by decide

-- This is NOT a vertical strip (row 2 has 3 boxes: 7-4=3 > 1)
example : ¬exampleA.isVerticalStrip := by decide

-- This is a horizontal 6-strip
example : exampleA.isHorizontalNStrip 6 := by decide

/-- Example (b) from the textbook: λ = (3,3,2,1), μ = (2,2,1,0).
    This is a vertical 4-strip but NOT a horizontal strip. -/
def exampleB_outer : NPartition 4 where
  parts := ![3, 3, 2, 1]
  weaklyDecreasing := by decide

def exampleB_inner : NPartition 4 where
  parts := ![2, 2, 1, 0]
  weaklyDecreasing := by decide

def exampleB : SkewPartition 4 where
  outer := exampleB_outer
  inner := exampleB_inner
  contained := by decide

-- This is a vertical strip (each row has at most 1 box: λᵢ ≤ μᵢ + 1)
example : exampleB.isVerticalStrip := by decide

-- This is NOT a horizontal strip (column 3 has 2 boxes)
example : ¬exampleB.isHorizontalStrip := by decide

-- This is a vertical 4-strip
example : exampleB.isVerticalNStrip 4 := by decide

/-- Example (c) from the textbook: λ = (4,3,1,1), μ = (3,2,1,0).
    This is BOTH a horizontal 3-strip AND a vertical 3-strip. -/
def exampleC_outer : NPartition 4 where
  parts := ![4, 3, 1, 1]
  weaklyDecreasing := by decide

def exampleC_inner : NPartition 4 where
  parts := ![3, 2, 1, 0]
  weaklyDecreasing := by decide

def exampleC : SkewPartition 4 where
  outer := exampleC_outer
  inner := exampleC_inner
  contained := by decide

-- This is both horizontal and vertical
example : exampleC.isHorizontalStrip := by decide
example : exampleC.isVerticalStrip := by decide

-- This is both a horizontal 3-strip and a vertical 3-strip
example : exampleC.isHorizontalNStrip 3 := by decide
example : exampleC.isVerticalNStrip 3 := by decide

/-- Example (d) from the textbook: λ = (3,3,2,1), μ = (1,1,1,1).
    This is NEITHER a horizontal strip NOR a vertical strip. -/
def exampleD_outer : NPartition 4 where
  parts := ![3, 3, 2, 1]
  weaklyDecreasing := by decide

def exampleD_inner : NPartition 4 where
  parts := ![1, 1, 1, 1]
  weaklyDecreasing := by decide

def exampleD : SkewPartition 4 where
  outer := exampleD_outer
  inner := exampleD_inner
  contained := by decide

-- This is neither horizontal nor vertical
example : ¬exampleD.isHorizontalStrip := by decide
example : ¬exampleD.isVerticalStrip := by decide

end Examples

end SkewPartition
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

/-- The monomial x^T associated to a tableau T.
    x_T = ∏_{(i,j) ∈ Y(λ)} x_{T(i,j)} -/
noncomputable def SSYT.toMonomial {lam : NPartition N} (T : SSYT lam) :
    MvPolynomial (Fin N) R :=
  ∏ i : Fin N, ∏ j : Fin (lam.parts i), MvPolynomial.X (T.entries i j)

/-- Two skew SSYT are equal if their entries are equal. -/
theorem SkewSSYT.eq_of_entries_eq {s : SkewPartition N} {T1 T2 : SkewSSYT s}
    (h : T1.entries = T2.entries) : T1 = T2 := by
  cases T1; cases T2
  simp only at h
  subst h
  rfl

/-- For N = 1, all SkewSSYT of a given shape are equal.
    This is because all entries must be in Fin 1 = {0}, so there's only one possible entry.
    This is useful for proving special cases of the Bender-Knuth bijection. -/
instance SkewSSYT.instSubsingletonOne (s : SkewPartition 1) : Subsingleton (SkewSSYT s) := by
  constructor
  intro T1 T2
  apply SkewSSYT.eq_of_entries_eq
  funext i k
  exact Subsingleton.elim (T1.entries i k) (T2.entries i k)

/-- The monomial x^T associated to a skew tableau T. -/
noncomputable def SkewSSYT.toMonomial {s : SkewPartition N} (T : SkewSSYT s) :
    MvPolynomial (Fin N) R :=
  ∏ i : Fin N, ∏ j : Fin (s.outer.parts i - s.inner.parts i),
    MvPolynomial.X (T.entries i j)

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

/-!
### Finiteness of SSYT

The set of semistandard Young tableaux of a given shape is finite because:
1. The shape has finitely many cells
2. Each cell can contain one of finitely many values (elements of Fin N)
3. The SSYT conditions (row-weak, column-strict) define a subset of all fillings
-/


/-- A filling of a skew shape is a function assigning a value in Fin N to each cell.
    We use `abbrev` instead of `def` to ensure type class inference can see through this. -/
abbrev SkewFilling (s : SkewPartition N) :=
  (i : Fin N) → (k : Fin (s.outer.parts i - s.inner.parts i)) → Fin N

/-- The type of fillings of a skew shape is finite. -/
instance skewFilling_fintype (s : SkewPartition N) : Fintype (SkewFilling s) := inferInstance

/-- Predicate for a filling satisfying the SSYT row-weak condition. -/
def isRowWeak (s : SkewPartition N) (f : SkewFilling s) : Prop :=
  ∀ i : Fin N, ∀ j k : Fin (s.outer.parts i - s.inner.parts i),
    j ≤ k → f i j ≤ f i k

/-- Predicate for a filling satisfying the SSYT column-strict condition.
    This is a simplified version that checks the condition for adjacent rows. -/
def isColStrict (s : SkewPartition N) (f : SkewFilling s) : Prop :=
  ∀ i : Fin N, ∀ hi : i.val + 1 < N,
    ∀ k : Fin (s.outer.parts i - s.inner.parts i),
    ∀ _hcol : s.inner.parts i + k.val + 1 > s.inner.parts ⟨i.val + 1, hi⟩ ∧
             s.inner.parts i + k.val + 1 ≤ s.outer.parts ⟨i.val + 1, hi⟩,
    let k' : ℕ := s.inner.parts i + k.val - s.inner.parts ⟨i.val + 1, hi⟩
    ∀ hk' : k' < s.outer.parts ⟨i.val + 1, hi⟩ - s.inner.parts ⟨i.val + 1, hi⟩,
    f i k < f ⟨i.val + 1, hi⟩ ⟨k', hk'⟩

/-- Combined predicate for SSYT conditions. -/
def isSSYTFilling (s : SkewPartition N) (f : SkewFilling s) : Prop :=
  isRowWeak s f ∧ isColStrict s f

/-- The row-weak predicate is decidable. -/
instance isRowWeak_decidable (s : SkewPartition N) (f : SkewFilling s) :
    Decidable (isRowWeak s f) :=
  Fintype.decidableForallFintype

/-- The column-strict predicate is decidable. -/
instance isColStrict_decidable (s : SkewPartition N) (f : SkewFilling s) :
    Decidable (isColStrict s f) :=
  Fintype.decidableForallFintype

/-- The SSYT predicate is decidable. -/
instance isSSYTFilling_decidable (s : SkewPartition N) (f : SkewFilling s) :
    Decidable (isSSYTFilling s f) :=
  instDecidableAnd

/-- The finite set of all fillings satisfying SSYT conditions. -/
noncomputable def ssytFillingFinset (s : SkewPartition N) : Finset (SkewFilling s) :=
  Finset.univ.filter (isSSYTFilling s)

/-- Convert a SkewSSYT to a filling. -/
def SkewSSYT.toFilling {s : SkewPartition N} (T : SkewSSYT s) : SkewFilling s :=
  T.entries

/-- A filling satisfying SSYT conditions can be converted to a SkewSSYT. -/
def fillingToSkewSSYT {s : SkewPartition N} (f : SkewFilling s)
    (hf : isSSYTFilling s f) : SkewSSYT s where
  entries := f
  rowWeak := hf.1
  colStrict := hf.2

/-- A filling of a non-skew shape λ. -/
abbrev Filling (lam : NPartition N) := (i : Fin N) → Fin (lam.parts i) → Fin N

/-- Fintype instance for fillings of non-skew shapes. -/
instance filling_fintype (lam : NPartition N) : Fintype (Filling lam) := inferInstance

/-- Row-weak predicate for fillings of non-skew shapes. -/
def isRowWeakFilling (lam : NPartition N) (f : Filling lam) : Prop :=
  ∀ i : Fin N, ∀ j k : Fin (lam.parts i), j ≤ k → f i j ≤ f i k

/-- Column-strict predicate for fillings of non-skew shapes. -/
def isColStrictFilling (lam : NPartition N) (f : Filling lam) : Prop :=
  ∀ i : Fin N, ∀ hi : i.val + 1 < N, ∀ j : Fin (lam.parts i),
    ∀ hj : j.val < (lam.parts ⟨i.val + 1, hi⟩),
    f i j < f ⟨i.val + 1, hi⟩ ⟨j.val, hj⟩

/-- Combined SSYT predicate for non-skew fillings. -/
def isSSYTFillingNonSkew (lam : NPartition N) (f : Filling lam) : Prop :=
  isRowWeakFilling lam f ∧ isColStrictFilling lam f

/-- Decidability of row-weak for non-skew fillings. -/
instance isRowWeakFilling_decidable (lam : NPartition N) (f : Filling lam) :
    Decidable (isRowWeakFilling lam f) := Fintype.decidableForallFintype

/-- Decidability of column-strict for non-skew fillings. -/
instance isColStrictFilling_decidable (lam : NPartition N) (f : Filling lam) :
    Decidable (isColStrictFilling lam f) := Fintype.decidableForallFintype

/-- Decidability of SSYT predicate for non-skew fillings. -/
instance isSSYTFillingNonSkew_decidable (lam : NPartition N) (f : Filling lam) :
    Decidable (isSSYTFillingNonSkew lam f) := instDecidableAnd

/-- Finset of valid fillings for non-skew shapes. -/
noncomputable def ssytFillingFinsetNonSkew (lam : NPartition N) : Finset (Filling lam) :=
  Finset.univ.filter (isSSYTFillingNonSkew lam)

/-- Convert a valid filling to an SSYT. -/
def fillingToSSYT (lam : NPartition N) (f : Filling lam)
    (hf : isSSYTFillingNonSkew lam f) : SSYT lam where
  entries := f
  rowWeak := hf.1
  colStrict := hf.2

/-- The set of all SSYT of shape λ.
    This is finite because it's a subset of all fillings, which is finite. -/
noncomputable def ssytFinset (lam : NPartition N) : Finset (SSYT lam) :=
  (ssytFillingFinsetNonSkew lam).attach.map ⟨
    fun ⟨f, hf⟩ => fillingToSSYT lam f (Finset.mem_filter.mp hf).2,
    fun ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ h => by
      simp only [Subtype.mk.injEq]
      have : (fillingToSSYT lam f₁ (Finset.mem_filter.mp hf₁).2).entries =
             (fillingToSSYT lam f₂ (Finset.mem_filter.mp hf₂).2).entries := by
        simp only [fillingToSSYT] at h
        cases h
        rfl
      exact this
  ⟩

/-- The set of all skew SSYT of shape λ/μ.
    This is finite because it's a subset of all fillings, which is finite. -/
noncomputable def skewSSYTFinset (s : SkewPartition N) : Finset (SkewSSYT s) :=
  -- We construct this by mapping from the finite set of valid fillings
  -- The noncomputable is needed because we need to construct SkewSSYT from fillings
  (ssytFillingFinset s).attach.map ⟨
    fun ⟨f, hf⟩ => fillingToSkewSSYT f (Finset.mem_filter.mp hf).2,
    fun ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ h => by
      simp only [Subtype.mk.injEq]
      have : (fillingToSkewSSYT f₁ (Finset.mem_filter.mp hf₁).2).entries =
             (fillingToSkewSSYT f₂ (Finset.mem_filter.mp hf₂).2).entries := by
        simp only [fillingToSkewSSYT] at h
        cases h
        rfl
      exact this
  ⟩

/-- A SkewSSYT's entries form a valid SSYT filling. -/
theorem SkewSSYT.toFilling_isSSYTFilling {s : SkewPartition N} (T : SkewSSYT s) :
    isSSYTFilling s T.toFilling := ⟨T.rowWeak, T.colStrict⟩

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

instance (f : Fin N → ℕ) : Decidable (isWeaklyDecreasing f) :=
  Fintype.decidableForallFintype

/-- Check if |λ| - |μ| = n. -/
def hasSizeDiff (mu lam : Fin N → ℕ) (n : ℕ) : Prop :=
  (∑ i, lam i) = (∑ i, mu i) + n

instance (mu lam : Fin N → ℕ) (n : ℕ) : Decidable (hasSizeDiff mu lam n) :=
  inferInstanceAs (Decidable (_ = _))

/-- A skew partition λ/μ is a horizontal strip if no two boxes lie in the same column.
    Equivalently: μ_i ≥ λ_{i+1} for all i.

    The argument order `(lam, mu)` matches standard mathematical notation λ/μ.

    **Related definitions:**
    - `SkewPartition.isHorizontalStrip`: Bundled version for `SkewPartition N` -/
def isHorizontalStripFun (lam mu : Fin N → ℕ) : Prop :=
  ∀ i : Fin N, ∀ hi : i.val + 1 < N, mu i ≥ lam ⟨i.val + 1, hi⟩

/-- A skew partition λ/μ is a vertical strip if no two boxes lie in the same row.
    Equivalently: λ_i ≤ μ_i + 1 for all i.

    The argument order `(lam, mu)` matches standard mathematical notation λ/μ.

    **Related definitions:**
    - `SkewPartition.isVerticalStrip`: Bundled version for `SkewPartition N` -/
def isVerticalStripFun (lam mu : Fin N → ℕ) : Prop :=
  ∀ i : Fin N, lam i ≤ mu i + 1

/-- Decidable instance for horizontal strip predicate. -/
instance instDecidableIsHorizontalStripFun (lam mu : Fin N → ℕ) :
    Decidable (isHorizontalStripFun lam mu) :=
  Fintype.decidableForallFintype

/-- Decidable instance for vertical strip predicate. -/
instance instDecidableIsVerticalStripFun (lam mu : Fin N → ℕ) :
    Decidable (isVerticalStripFun lam mu) :=
  Fintype.decidableForallFintype

/-- Convert a valid function to an NPartition. -/
def toNPartition (f : Fin N → ℕ) (hf : isWeaklyDecreasing f) : NPartition N where
  parts := f
  weaklyDecreasing := hf

/-- The set of N-partitions λ such that λ/μ is a horizontal n-strip.

    This is the set of all N-partitions λ satisfying:
    1. μ ⊆ λ (containment): μ_i ≤ λ_i for all i
    2. Horizontal strip: μ_i ≥ λ_{i+1} for all i < N
    3. Size: |λ| - |μ| = n

    The set is finite because each λ_i is bounded. -/
def horizontalNStripPartitions (mu : NPartition N) (n : ℕ) : Finset (NPartition N) :=
  (potentialHorizontalStrips mu n).filter (fun f =>
    isWeaklyDecreasing f ∧ isHorizontalStripFun f mu.parts ∧ hasSizeDiff mu.parts f n
  ) |>.attach.image (fun ⟨f, hf⟩ =>
    let hf' := Finset.mem_filter.mp hf
    toNPartition f hf'.2.1)

/-- The bound for each λ_i when forming a vertical strip with μ.
    λ_i must satisfy μ_i ≤ λ_i ≤ μ_i + 1 (vertical strip condition). -/
def verticalStripUpperBound (mu : NPartition N) (i : Fin N) : ℕ :=
  mu.parts i + 1

/-- A function from Fin N to ℕ that could potentially form a vertical n-strip with μ. -/
def potentialVerticalStrips (mu : NPartition N) : Finset (Fin N → ℕ) :=
  Fintype.piFinset (fun i => Finset.Icc (mu.parts i) (verticalStripUpperBound mu i))

/-- The set of N-partitions λ such that λ/μ is a vertical n-strip.

    This is the set of all N-partitions λ satisfying:
    1. μ ⊆ λ (containment): μ_i ≤ λ_i for all i
    2. Vertical strip: λ_i ≤ μ_i + 1 for all i
    3. Size: |λ| - |μ| = n

    The set is finite because each λ_i ∈ {μ_i, μ_i + 1}. -/
def verticalNStripPartitions (mu : NPartition N) (n : ℕ) : Finset (NPartition N) :=
  (potentialVerticalStrips mu).filter (fun f =>
    isWeaklyDecreasing f ∧ isVerticalStripFun f mu.parts ∧ hasSizeDiff mu.parts f n
  ) |>.attach.image (fun ⟨f, hf⟩ =>
    let hf' := Finset.mem_filter.mp hf
    toNPartition f hf'.2.1)
/-!
### Properties of Horizontal Strip Partitions
-/
/-!
### Properties of Vertical Strip Partitions
-/
/-!
### Membership Characterization for Strip Partitions

These theorems provide complete characterizations of membership in
`horizontalNStripPartitions` and `verticalNStripPartitions`, useful for
proving that specific partitions belong to these sets.
-/
/-!
### Infrastructure for Pieri Rule Proofs

The Pieri rules require a bijection between:
- Domain: `Sym (Fin N) n × SSYT μ` (multisets of size n paired with tableaux of shape μ)
- Codomain: `⨆_{λ ∈ horizontalNStripPartitions μ n} SSYT λ` (tableaux of shapes forming horizontal n-strips)

This bijection is the RSK row insertion. Below we provide lemmas that show how the
RHS of the Pieri rule can be rewritten as a sum over a sigma type, making the
structure of the proof clear.
-/
/-!
### Alternative Approach: Pieri Rules via Littlewood-Richardson

An alternative proof of the Pieri rules derives them from the Littlewood-Richardson rule.
The key observations are:

1. **h_n = s_{(n,0,...,0)}**: The complete homogeneous symmetric polynomial h_n equals
   the Schur polynomial indexed by the row partition (n, 0, ..., 0).

2. **e_n = s_{(1,1,...,1,0,...,0)}**: The elementary symmetric polynomial e_n equals
   the Schur polynomial indexed by the column partition with n ones.

3. **Littlewood-Richardson specialization**: When ν = (n, 0, ..., 0), the ν-Yamanouchi
   tableaux of shape λ/μ correspond exactly to horizontal n-strips (or vertical n-strips
   for the column partition case).

The infrastructure for this approach requires:
- `NPartition.rowPartition`: The partition (n, 0, ..., 0) ✓ (defined above)
- `NPartition.colPartition`: The partition (1, 1, ..., 1, 0, ..., 0) ✓ (defined above)
- `hsymm_eq_schur_rowPartition`: h_n = s_{rowPartition} ✓ (proved below)
- `esymm_eq_schur_colPartition`: e_n = s_{colPartition} ✓ (proved below)
- Characterization of Yamanouchi tableaux for row/column partitions (partial: reverse direction proved)

This approach is documented in Exercise exe.sf.pieri of the source text.
The Pieri rules themselves are left as exercises (see `pieri_horizontal`, `pieri_vertical`).
-/
/-! ### Yamanouchi Tableaux Infrastructure for Row/Column Partitions

This section provides infrastructure for working with row and column partitions
in the context of Yamanouchi tableaux (defined in `LittlewoodRichardson.lean`).

**Mathematical Background:**

The key insight connecting the Littlewood-Richardson rule to Pieri rules is that
Yamanouchi tableaux for row and column partitions have a simple characterization:

**For row partition ν = (n, 0, ..., 0):**
A semistandard tableau T of shape λ/μ is ν-Yamanouchi iff:
1. All entries of T are 0 (the first row index)
2. λ/μ is a horizontal strip (no two cells in same column)

This is because:
- The Yamanouchi condition requires ν + cont(col_{≥j}(T)) to be weakly decreasing for all j > 0
- For ν = (n, 0, ..., 0), adding any content to position i > 0 would violate this
- So all entries must be 0, and semistandardness forces at most one cell per column

**For column partition ν = (1, 1, ..., 1, 0, ..., 0) with n ones:**
A semistandard tableau T of shape λ/μ is ν-Yamanouchi iff:
1. Entries form a valid "staircase" pattern (entry in row i is at least i)
2. λ/μ is a vertical strip (no two cells in same row)

This is because:
- The Yamanouchi condition with column partition ensures votes are spread across rows
- Semistandardness with at most one entry per row gives vertical strip

**What's provided here:**
- `rowPartitionFun`, `colPartitionFun`: Functions extracting partition parts
- Simp lemmas for accessing row/column partition values
- Proofs that these are valid N-partitions

**Note:** The reverse direction `allEntriesZero_implies_isYamanouchi_rowPartition` is proved below:
for row partition ν = (n, 0, ..., 0), if all entries of a semistandard tableau are 0,
then it is ν-Yamanouchi.
-/


/-- Row partition as a function (for use with LittlewoodRichardson.IsYamanouchi). -/
def rowPartitionFun (N : ℕ) (n : ℕ) (hN : 0 < N) : Fin N → ℕ :=
  (NPartition.rowPartition N n hN).parts

/-- Column partition as a function (for use with LittlewoodRichardson.IsYamanouchi). -/
def colPartitionFun (N : ℕ) (n : ℕ) (hn : n ≤ N) : Fin N → ℕ :=
  (NPartition.colPartition N n hn).parts
/-! ### Yamanouchi Tableaux Characterization for Row/Column Partitions

This section provides the key characterization theorems connecting Yamanouchi tableaux
with horizontal and vertical strips. These theorems enable the alternative proof of
Pieri rules via the Littlewood-Richardson rule.

**Mathematical Background:**

For the row partition ν = (n, 0, ..., 0):
- A semistandard tableau T of shape λ/μ is ν-Yamanouchi iff all entries are 0
  and λ/μ is a horizontal strip.
- This is because adding any content to position i > 0 would violate the
  weakly decreasing property of ν + cont(col_{≥j}(T)).

For the column partition ν = (1, 1, ..., 1, 0, ..., 0) with n ones:
- A semistandard tableau T of shape λ/μ is ν-Yamanouchi iff entries follow
  a specific pattern and λ/μ is a vertical strip.
-/
/-!
### Equivalences Between Strip Definitions

The following lemmas establish equivalences between the bundled and unbundled
representations of horizontal/vertical strip predicates:

1. **Bundled:** `SkewPartition.isHorizontalStrip` / `SkewPartition.isVerticalStrip`
   - Input: `SkewPartition N` (bundled outer/inner partitions)
   - Used in: Main theorems like `pieri_horizontal`, `pieri_vertical`

2. **Unbundled (canonical):** `isHorizontalStripFun` / `isVerticalStripFun`
   - Input: `(lam mu : Fin N → ℕ)` with argument order `(lam, mu)` matching λ/μ notation
   - Used in: `horizontalNStripPartitions`, `verticalNStripPartitions`, and
     integration with `LittlewoodRichardson.Tableau`
-/

/-- All entries of a tableau are 0 (the first row index).
    This is the key property for row partition Yamanouchi tableaux. -/
def allEntriesZero {lam mu : Fin N → ℕ} (T : AlgebraicCombinatorics.Tableau lam mu) : Prop :=
  ∀ c : {c : Fin N × ℕ // c ∈ AlgebraicCombinatorics.skewYoungDiagram lam mu}, (T c).val = 0

/-- Decidable instance for allEntriesZero when the diagram is finite. -/
noncomputable instance instDecidableAllEntriesZero {lam mu : Fin N → ℕ}
    (T : AlgebraicCombinatorics.Tableau lam mu) : Decidable (allEntriesZero T) := by
  haveI : Fintype {c : Fin N × ℕ // c ∈ AlgebraicCombinatorics.skewYoungDiagram lam mu} :=
    Set.Finite.fintype (AlgebraicCombinatorics.skewYoungDiagram_finite lam mu)
  exact Fintype.decidableForallFintype
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

/-- A lattice path in ℤ² from (a, 1) to (c, N) using north and east steps.
    This is the type of paths relevant for the Jacobi-Trudi proof. -/
structure LatticePath (a c : ℤ) where
  /-- The sequence of heights at which east-steps are taken.
      A path from (a, 1) to (c, N) has exactly (c - a) east-steps
      (when c ≥ a), and each east-step occurs at some height in [1, N]. -/
  eastStepHeights : List (Fin N)
  /-- The heights form a weakly increasing sequence (path goes north or east) -/
  weaklyIncreasing : eastStepHeights.IsChain (· ≤ ·)
  /-- The number of east-steps equals c - a (when non-negative) -/
  length_eq : eastStepHeights.length = (c - a).toNat

/-- The weight of a lattice path is the product of x_j for each east-step at height j.
    This corresponds to the weight function w in the source. -/
noncomputable def LatticePath.weight {a c : ℤ} (p : LatticePath (N := N) a c) :
    MvPolynomial (Fin N) R :=
  (p.eastStepHeights.map (fun j => MvPolynomial.X j)).prod

/-- Extensionality lemma for lattice paths. -/
@[ext]
theorem LatticePath.ext {a c : ℤ} {p q : LatticePath (N := N) a c}
    (h : p.eastStepHeights = q.eastStepHeights) : p = q := by
  cases p; cases q; simp_all

/-- Convert a lattice path to a Sym element (multiset of heights). -/
def LatticePath.toSym {a c : ℤ} (p : LatticePath (N := N) a c) : Sym (Fin N) (c - a).toNat :=
  ⟨↑p.eastStepHeights, by simp [p.length_eq]⟩

/-- Convert a Sym element (multiset) to a lattice path by sorting. -/
noncomputable def symToLatticePath {a c : ℤ} (s : Sym (Fin N) (c - a).toNat) :
    LatticePath (N := N) a c where
  eastStepHeights := s.1.sort (· ≤ ·)
  weaklyIncreasing := List.Pairwise.isChain (Multiset.pairwise_sort s.1 (· ≤ ·))
  length_eq := by rw [Multiset.length_sort]; exact s.2

/-- Converting a path to Sym and back gives the original path. -/
theorem symToLatticePath_toSym {a c : ℤ} (p : LatticePath (N := N) a c) :
    symToLatticePath (p.toSym) = p := by
  apply LatticePath.ext
  simp only [symToLatticePath, LatticePath.toSym]
  have hsort_eq : ((↑p.eastStepHeights : Multiset (Fin N)).sort (· ≤ ·) : Multiset (Fin N)) =
                  (↑p.eastStepHeights : Multiset (Fin N)) :=
    Multiset.sort_eq (↑p.eastStepHeights : Multiset (Fin N)) (· ≤ ·)
  have hperm : ((↑p.eastStepHeights : Multiset (Fin N)).sort (· ≤ ·)).Perm p.eastStepHeights :=
    Quotient.exact hsort_eq
  exact hperm.eq_of_pairwise' (Multiset.pairwise_sort (↑p.eastStepHeights : Multiset (Fin N)) (· ≤ ·))
                               p.weaklyIncreasing.pairwise

/-- Converting a Sym to a path and back gives the original Sym. -/
theorem toSym_symToLatticePath {a c : ℤ} (s : Sym (Fin N) (c - a).toNat) :
    (symToLatticePath s).toSym = s := by
  apply Sym.coe_injective
  simp only [LatticePath.toSym, symToLatticePath, Sym.coe_mk]
  exact Multiset.sort_eq s.1 (· ≤ ·)

/-- The equivalence between lattice paths and Sym (multisets). -/
noncomputable def latticePathSymEquiv {a c : ℤ} :
    LatticePath (N := N) a c ≃ Sym (Fin N) (c - a).toNat where
  toFun := LatticePath.toSym
  invFun := symToLatticePath
  left_inv := symToLatticePath_toSym
  right_inv := toSym_symToLatticePath

/-- Fintype instance for LatticePath via the equivalence with Sym. -/
noncomputable instance {a c : ℤ} : Fintype (LatticePath (N := N) a c) :=
  Fintype.ofEquiv _ latticePathSymEquiv.symm

/-- The set of all lattice paths from (a, 1) to (c, N).
    Empty when c < a (no valid paths), otherwise all paths. -/
noncomputable def latticePathFinset (a c : ℤ) : Finset (LatticePath (N := N) a c) :=
  if 0 ≤ c - a then Finset.univ else ∅

/-- A non-intersecting path tuple (nipat) from sources A to targets B.
    For Jacobi-Trudi, A_i = (μᵢ - i, 1) and B_i = (λᵢ - i, N). -/
structure Nipat (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) where
  /-- The tuple of paths, one for each i ∈ [N] -/
  paths : (i : Fin N) → LatticePath (N := N)
    ((mu i : ℤ) - (i.val : ℤ)) ((lam i : ℤ) - (i.val : ℤ))
  /-- The paths satisfy column-strictness: for i < j, if east steps k (in path i)
      and k' (in path j) correspond to the same tableau column (mu i + k = mu j + k'),
      then the height of path i at step k is strictly less than the height of path j at step k'.
      This is the key property that makes the nipat-SSYT bijection work. -/
  colStrictPaths : ∀ i j : Fin N, i < j →
    ∀ k : ℕ, ∀ hk : k < (paths i).eastStepHeights.length,
    ∀ k' : ℕ, ∀ hk' : k' < (paths j).eastStepHeights.length,
    mu i + k = mu j + k' →
    (paths i).eastStepHeights[k] < (paths j).eastStepHeights[k']

/-- The weight of a nipat is the product of the weights of its component paths. -/
noncomputable def Nipat.weight {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np : Nipat lam mu hlam hmu hcontained) : MvPolynomial (Fin N) R :=
  ∏ i : Fin N, (np.paths i).weight

/-- Helper lemma: in a weakly increasing chain, elements at smaller indices are ≤ elements at larger indices. -/
theorem List.IsChain.getElem_le_getElem_of_le {α : Type*} [Preorder α]
    {l : List α} (h : l.IsChain (· ≤ ·)) {i j : ℕ} (hi : i < l.length) (hj : j < l.length)
    (hij : i ≤ j) : l[i] ≤ l[j] := by
  induction j with
  | zero => simp_all
  | succ j ih =>
    by_cases hj' : i = j + 1
    · simp [hj']
    · by_cases hij' : i ≤ j
      · have hj'' : j < l.length := by omega
        have h1 : l[i] ≤ l[j] := ih hj'' hij'
        rw [List.isChain_iff_getElem] at h
        have h2 := h j hj
        exact Trans.trans h1 h2
      · omega

/-- The bijection between nipats and SSYT, sending a nipat to the tableau
    whose i-th row contains the heights of east-steps in path i. -/
noncomputable def nipatToSSYT {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np : Nipat lam mu hlam hmu hcontained) :
    SkewSSYT ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩ where
  entries := fun i k => (np.paths i).eastStepHeights.get ⟨k.val, by
    have hlen : (np.paths i).eastStepHeights.length = lam i - mu i := by
      rw [(np.paths i).length_eq]
      simp only [sub_sub_sub_cancel_right]
      have h : mu i ≤ lam i := hcontained i
      omega
    rw [hlen]; exact k.isLt⟩
  rowWeak := fun i j k hjk => by
    simp only [List.get_eq_getElem]
    have hlen : (np.paths i).eastStepHeights.length = lam i - mu i := by
      rw [(np.paths i).length_eq]
      simp only [sub_sub_sub_cancel_right]
      have h : mu i ≤ lam i := hcontained i
      omega
    have hj_lt : j.val < (np.paths i).eastStepHeights.length := by rw [hlen]; exact j.isLt
    have hk_lt : k.val < (np.paths i).eastStepHeights.length := by rw [hlen]; exact k.isLt
    exact List.IsChain.getElem_le_getElem_of_le (np.paths i).weaklyIncreasing hj_lt hk_lt hjk
  colStrict := fun i hi k hcol hk' => by
    simp only [List.get_eq_getElem]
    -- Unfold the skew partition structure to get direct access to mu and lam
    simp only [] at hcol  -- normalizes hypothesis for omega
    -- Now hcol : mu i + k.val + 1 > mu (i+1) ∧ mu i + k.val + 1 ≤ lam (i+1)
    -- Use explicit index for row i+1
    have hij : i < (⟨i.val + 1, hi⟩ : Fin N) := by simp only [Fin.lt_def]; omega
    -- Path length for row i
    have hlen_i : (np.paths i).eastStepHeights.length = lam i - mu i := by
      rw [(np.paths i).length_eq]
      simp only [sub_sub_sub_cancel_right]
      simp
    have hk_lt : k.val < (np.paths i).eastStepHeights.length := by 
      rw [hlen_i]; exact k.isLt
    -- Path length for row i+1
    have hlen_j : (np.paths ⟨i.val + 1, hi⟩).eastStepHeights.length = 
        lam ⟨i.val + 1, hi⟩ - mu ⟨i.val + 1, hi⟩ := by
      rw [(np.paths ⟨i.val + 1, hi⟩).length_eq]
      simp only [sub_sub_sub_cancel_right]
      simp
    have hk'_lt : (mu i + k.val - mu ⟨i.val + 1, hi⟩) < 
        (np.paths ⟨i.val + 1, hi⟩).eastStepHeights.length := by 
      rw [hlen_j]
      have h1 := hcol.1
      have h2 := hcol.2
      omega
    -- The column condition: mu i + k = mu (i+1) + k'
    have hcol_eq : mu i + k.val = mu ⟨i.val + 1, hi⟩ + (mu i + k.val - mu ⟨i.val + 1, hi⟩) := by
      have h1 := hcol.1
      omega
    -- Apply colStrictPaths
    exact np.colStrictPaths i ⟨i.val + 1, hi⟩ hij k.val hk_lt 
      (mu i + k.val - mu ⟨i.val + 1, hi⟩) hk'_lt hcol_eq

/-- Helper to create a LatticePath from tableau entries for a single row.
    Given entries for row i of a tableau, creates the corresponding lattice path
    with east-steps at the heights given by the entries. -/
def mkLatticePathFromEntries (lam mu : ℕ) (i : ℕ)
    (entries : Fin (lam - mu) → Fin N)
    (hrowWeak : ∀ j k : Fin (lam - mu), j ≤ k → entries j ≤ entries k) :
    LatticePath (N := N) ((mu : ℤ) - (i : ℤ)) ((lam : ℤ) - (i : ℤ)) where
  eastStepHeights := List.ofFn entries
  weaklyIncreasing := by
    rw [List.isChain_iff_pairwise, List.pairwise_ofFn]
    intro j k hjk
    exact hrowWeak j k (le_of_lt hjk)
  length_eq := by
    simp only [List.length_ofFn, sub_sub_sub_cancel_right]
    simp

/-- The inverse bijection from SSYT to nipats, sending a tableau to the nipat
    whose i-th path has east-steps at the heights given by row i of the tableau. -/
noncomputable def ssytToNipat {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (T : SkewSSYT ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩) :
    Nipat lam mu hlam hmu hcontained where
  paths := fun i => mkLatticePathFromEntries (lam i) (mu i) i.val (T.entries i) (T.rowWeak i)
  colStrictPaths := fun i j hij k hk k' hk' hcol_eq => by
    -- Need to show: (paths i).eastStepHeights[k] < (paths j).eastStepHeights[k']
    -- This follows from T.colStrict_nonadjacent.
    -- The column condition hcol_eq : mu i + k = mu j + k' ensures we're in the same column.
    simp only [mkLatticePathFromEntries]
    rw [List.getElem_ofFn, List.getElem_ofFn]
    -- Convert bounds
    have hk_fin : k < lam i - mu i := by simp [mkLatticePathFromEntries] at hk; exact hk
    have hk'_fin : k' < lam j - mu j := by simp [mkLatticePathFromEntries] at hk'; exact hk'
    -- Apply the column-strict lemma for non-adjacent rows
    exact T.colStrict_nonadjacent i j hij ⟨k, hk_fin⟩ ⟨k', hk'_fin⟩ hcol_eq

/-- Two nipats with equal paths are equal. -/
theorem Nipat.eq_of_paths_eq {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np1 np2 : Nipat lam mu hlam hmu hcontained)
    (h : np1.paths = np2.paths) : np1 = np2 := by
  obtain ⟨p1, ni1⟩ := np1
  obtain ⟨p2, ni2⟩ := np2
  simp only at h
  subst h
  rfl

/-- ssytToNipat is a left inverse of nipatToSSYT. -/
theorem ssytToNipat_nipatToSSYT {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np : Nipat lam mu hlam hmu hcontained) :
    ssytToNipat (nipatToSSYT np) = np := by
  apply Nipat.eq_of_paths_eq
  funext i
  apply LatticePath.ext
  simp only [ssytToNipat, nipatToSSYT, mkLatticePathFromEntries]
  -- Need to show: List.ofFn (fun k => (np.paths i).eastStepHeights[k]) = (np.paths i).eastStepHeights
  have hlen : (np.paths i).eastStepHeights.length = lam i - mu i := by
    rw [(np.paths i).length_eq]
    simp only [sub_sub_sub_cancel_right]
    have h : mu i ≤ lam i := hcontained i
    omega
  -- The key is that List.ofFn of getElem gives back the original list
  -- We need to show the LHS equals the RHS by showing they have the same elements
  apply List.ext_getElem
  · simp only [List.length_ofFn, hlen]
  · intro n h1 h2
    simp only [List.getElem_ofFn, List.get_eq_getElem]

/-- The length of path i's eastStepHeights equals lam i - mu i. -/
theorem nipat_path_length {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np : Nipat lam mu hlam hmu hcontained) (i : Fin N) :
    (np.paths i).eastStepHeights.length = lam i - mu i := by
  rw [(np.paths i).length_eq]
  simp only [sub_sub_sub_cancel_right]
  have h : mu i ≤ lam i := hcontained i
  omega

/-- Specification lemma for nipatToSSYT: the entries of row i are the heights
    of the east-steps in path i. This captures the key property of the bijection. -/
theorem nipatToSSYT_entries {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np : Nipat lam mu hlam hmu hcontained) (i : Fin N) (k : Fin (lam i - mu i)) :
    (nipatToSSYT np).entries i k = (np.paths i).eastStepHeights.get ⟨k.val, by
      rw [nipat_path_length np i]; exact k.isLt⟩ := by
  simp only [nipatToSSYT, List.get_eq_getElem]

/-- Specification lemma for ssytToNipat: the east-step heights of path i are the entries
    of row i of the tableau. This is the inverse specification to nipatToSSYT_entries. -/
theorem ssytToNipat_paths {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (T : SkewSSYT ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩) (i : Fin N) (k : Fin (lam i - mu i)) :
    ((ssytToNipat T).paths i).eastStepHeights.get ⟨k.val, by
      rw [nipat_path_length (ssytToNipat T) i]; exact k.isLt⟩ = T.entries i k := by
  simp only [ssytToNipat, mkLatticePathFromEntries, List.get_ofFn]
  congr 1

/-- nipatToSSYT is a left inverse of ssytToNipat. -/
theorem nipatToSSYT_ssytToNipat {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (T : SkewSSYT ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩) :
    nipatToSSYT (ssytToNipat T) = T := by
  apply SkewSSYT.eq_of_entries_eq
  funext i k
  rw [nipatToSSYT_entries, ssytToNipat_paths]
/-! ### Fintype instance for Nipat via the bijection with SkewSSYT

The `Nipat` type is finite because it is in bijection with `SkewSSYT`, which is finite.
We establish this by constructing an equivalence using `nipatToSSYT` and `ssytToNipat`. -/


/-- Fintype instance for SkewSSYT via the equivalence with valid fillings. -/
noncomputable instance SkewSSYT.fintype (s : SkewPartition N) : Fintype (SkewSSYT s) := by
  let S := {f : SkewFilling s // isSSYTFilling s f}
  let e : S ≃ SkewSSYT s := {
    toFun := fun ⟨f, hf⟩ => fillingToSkewSSYT f hf
    invFun := fun T => ⟨T.entries, T.toFilling_isSSYTFilling⟩
    left_inv := fun ⟨f, hf⟩ => by simp [fillingToSkewSSYT]
    right_inv := fun T => by cases T; rfl
  }
  exact Fintype.ofEquiv S e

/-- The equivalence between Nipat and SkewSSYT, established by the bijection functions. -/
noncomputable def nipatSSYTEquiv (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    Nipat lam mu hlam hmu hcontained ≃
      SkewSSYT ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩ where
  toFun := nipatToSSYT
  invFun := ssytToNipat
  left_inv := ssytToNipat_nipatToSSYT
  right_inv := nipatToSSYT_ssytToNipat

/-- Fintype instance for Nipat via the equivalence with SkewSSYT. -/
noncomputable instance Nipat.fintype (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    Fintype (Nipat lam mu hlam hmu hcontained) :=
  Fintype.ofEquiv _ (nipatSSYTEquiv lam mu hlam hmu hcontained).symm

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

/-- Helper: x-coordinate is monotone along a path in the integer lattice -/
theorem x_coord_monotone_along_path (vertices : List (ℤ × ℤ))
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩))
    (h_ne : vertices ≠ []) :
    (vertices.head h_ne).1 ≤ (vertices.getLast h_ne).1 := by
  induction vertices with
  | nil => exact absurd rfl h_ne
  | cons v₀ vs ih =>
    cases vs with
    | nil => simp
    | cons v₁ rest =>
      have h_arc : LGV.integerLattice.arc v₀ v₁ := by
        have := h_arcs 0 (by simp : 0 + 1 < (v₀ :: v₁ :: rest).length)
        simp at this
        exact this
      have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
          LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
            ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
        intro i hi
        have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
        have := h_arcs (i + 1) hi'
        simp at this ⊢
        exact this
      have h_ne' : v₁ :: rest ≠ [] := List.cons_ne_nil v₁ rest
      have ih' := ih h_arcs' h_ne'
      simp only [List.head_cons, List.getLast_cons h_ne'] at ih' ⊢
      -- v₀.1 ≤ v₁.1 from the arc, and v₁.1 ≤ getLast.1 from IH
      rcases h_arc with ⟨hx, _⟩ | ⟨hx, _⟩
      · -- East-step: v₁.1 = v₀.1 + 1
        omega
      · -- North-step: v₁.1 = v₀.1
        omega

/-- The number of east-steps equals the x-displacement.
    This is a key property for the bijection. -/
theorem lgvPathEastStepYCoords_length_eq_xDisplacement (vertices : List (ℤ × ℤ))
    (h_ne : vertices ≠ [])
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩)) :
    (lgvPathEastStepYCoords vertices).length =
      ((vertices.getLast h_ne).1 - (vertices.head h_ne).1).toNat := by
  -- Each east-step increases x by 1, north-steps don't change x
  -- So total east-steps = final x - initial x
  induction vertices with
  | nil => exact absurd rfl h_ne
  | cons v₀ vs ih =>
    cases vs with
    | nil =>
      simp [lgvPathEastStepYCoords]
    | cons v₁ rest =>
      have h_arc : LGV.integerLattice.arc v₀ v₁ := by
        have := h_arcs 0 (by simp : 0 + 1 < (v₀ :: v₁ :: rest).length)
        simp at this
        exact this
      have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
          LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
            ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
        intro i hi
        have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
        have := h_arcs (i + 1) hi'
        simp at this ⊢
        exact this
      have h_ne' : v₁ :: rest ≠ [] := List.cons_ne_nil v₁ rest
      have ih' := ih h_ne' h_arcs'
      -- Get the monotonicity bound for toNat
      have h_mono := x_coord_monotone_along_path (v₁ :: rest) h_arcs' h_ne'
      simp only [List.head_cons] at h_mono
      simp only [lgvPathEastStepYCoords]
      rcases h_arc with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · -- East-step: v₁.1 = v₀.1 + 1 ∧ v₁.2 = v₀.2
        simp only [hx, hy, and_self, ↓reduceIte, List.length_cons]
        rw [ih']
        simp only [List.head_cons, List.getLast_cons h_ne']
        -- Need: (getLast.1 - v₁.1).toNat + 1 = (getLast.1 - v₀.1).toNat
        -- where v₁.1 = v₀.1 + 1
        -- From h_mono: v₁.1 ≤ getLast.1, i.e., v₀.1 + 1 ≤ getLast.1
        omega
      · -- North-step: v₁.1 = v₀.1 ∧ v₁.2 = v₀.2 + 1
        have h_not_east : ¬(v₁.1 = v₀.1 + 1 ∧ v₁.2 = v₀.2) := by omega
        simp only [h_not_east, ↓reduceIte]
        rw [ih']
        simp only [List.head_cons, List.getLast_cons h_ne']
        -- Since v₁.1 = v₀.1, the toNat expressions are equal
        congr 1
        omega

/-- Helper lemma: y-coordinates are non-decreasing along any path in the integer lattice. -/
theorem lgvPath_y_nondecreasing (vertices : List (ℤ × ℤ))
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩))
    (i j : ℕ) (hi : i < vertices.length) (hj : j < vertices.length) (hij : i ≤ j) :
    (vertices.get ⟨i, hi⟩).2 ≤ (vertices.get ⟨j, hj⟩).2 := by
  induction j with
  | zero => simp_all
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hik
    · rfl
    · have hk : k < vertices.length := Nat.lt_of_succ_lt hj
      have hik' : i ≤ k := Nat.lt_succ_iff.mp hik
      have h1 := ih hk hik'
      have harc := h_arcs k hj
      simp only [LGV.integerLattice] at harc
      rcases harc with ⟨_, hy⟩ | ⟨_, hy⟩ <;> omega

/-- Helper lemma: all y-coordinates in lgvPathEastStepYCoords are y-coordinates of vertices. -/
theorem lgvPathEastStepYCoords_mem (vertices : List (ℤ × ℤ)) (y : ℤ)
    (hy : y ∈ lgvPathEastStepYCoords vertices) :
    ∃ i : ℕ, ∃ hi : i < vertices.length, (vertices.get ⟨i, hi⟩).2 = y := by
  induction vertices with
  | nil => simp [lgvPathEastStepYCoords] at hy
  | cons v₀ tl ih =>
    cases tl with
    | nil => simp [lgvPathEastStepYCoords] at hy
    | cons v₁ rest =>
      simp only [lgvPathEastStepYCoords] at hy
      split_ifs at hy with h_east
      · cases hy with
        | head =>
          exact ⟨0, by simp, rfl⟩
        | tail _ hmem =>
          obtain ⟨i, hi, heq⟩ := ih hmem
          simp only [List.length_cons] at hi
          have hi' : i + 1 < (v₀ :: v₁ :: rest).length := by simp; omega
          refine ⟨i + 1, hi', ?_⟩
          simp only [List.get_eq_getElem]
          have : (v₀ :: v₁ :: rest)[i + 1]'hi' = (v₁ :: rest)[i]'hi := by simp
          rw [this, ← heq]
          simp [List.get_eq_getElem]
      · obtain ⟨i, hi, heq⟩ := ih hy
        simp only [List.length_cons] at hi
        have hi' : i + 1 < (v₀ :: v₁ :: rest).length := by simp; omega
        refine ⟨i + 1, hi', ?_⟩
        simp only [List.get_eq_getElem]
        have : (v₀ :: v₁ :: rest)[i + 1]'hi' = (v₁ :: rest)[i]'hi := by simp
        rw [this, ← heq]
        simp [List.get_eq_getElem]

/-- Helper lemma: head of lgvPathEastStepYCoords is a y-coordinate of some vertex. -/
theorem lgvPathEastStepYCoords_head_mem (vertices : List (ℤ × ℤ)) (y : ℤ)
    (hy : y ∈ (lgvPathEastStepYCoords vertices).head?) :
    ∃ i : ℕ, ∃ hi : i < vertices.length, (vertices.get ⟨i, hi⟩).2 = y := by
  have hmem : y ∈ lgvPathEastStepYCoords vertices := by
    cases h : lgvPathEastStepYCoords vertices with
    | nil => simp [h] at hy
    | cons hd tl => simp [h] at hy; rw [hy]; simp
  exact lgvPathEastStepYCoords_mem vertices y hmem

/-- East-step y-coordinates are weakly increasing (paths go north or east). -/
theorem lgvPathEastStepYCoords_weaklyIncreasing (vertices : List (ℤ × ℤ))
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩)) :
    (lgvPathEastStepYCoords vertices).IsChain (· ≤ ·) := by
  -- The proof proceeds by induction on the vertex list.
  -- For each east-step, we show its y-coordinate is ≤ the next east-step's y-coordinate
  -- because y can only increase (north-steps) or stay the same (east-steps) along the path.
  induction vertices with
  | nil => exact List.isChain_nil
  | cons v₀ tl ih =>
    cases tl with
    | nil => exact List.isChain_nil
    | cons v₁ rest =>
      simp only [lgvPathEastStepYCoords]
      split_ifs with h_east
      · -- v₀ → v₁ is an east-step
        have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
            LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
          exact h_arcs (i + 1) hi'
        have ih' := ih h_arcs'
        rw [List.isChain_cons]
        constructor
        · -- Show v₀.2 ≤ head of lgvPathEastStepYCoords (v₁ :: rest)
          intro y hy
          obtain ⟨i, hi, heq⟩ := lgvPathEastStepYCoords_head_mem (v₁ :: rest) y hy
          -- v₀.2 = v₁.2 (from east-step) and v₁.2 ≤ (v₁ :: rest)[i].2 by monotonicity
          have hv01 : v₀.2 = v₁.2 := h_east.2.symm
          have hmono := lgvPath_y_nondecreasing (v₁ :: rest) h_arcs' 0 i (by simp) hi (Nat.zero_le _)
          simp at hmono
          rw [hv01, ← heq]
          exact hmono
        · exact ih'
      · -- v₀ → v₁ is a north-step, so the result is just lgvPathEastStepYCoords (v₁ :: rest)
        have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
            LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
          exact h_arcs (i + 1) hi'
        exact ih h_arcs'

/-- East-step y-coordinates are bounded between start and end y-coordinates. -/
theorem lgvPathEastStepYCoords_bounded (vertices : List (ℤ × ℤ))
    (h_ne : vertices ≠ [])
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩))
    (y : ℤ) (hy : y ∈ lgvPathEastStepYCoords vertices) :
    (vertices.head h_ne).2 ≤ y ∧ y ≤ (vertices.getLast h_ne).2 := by
  -- y is a y-coordinate of some vertex
  obtain ⟨i, hi, heq⟩ := lgvPathEastStepYCoords_mem vertices y hy
  constructor
  · -- head.2 ≤ y
    have h_head : (vertices.head h_ne).2 = (vertices.get ⟨0, List.length_pos_of_ne_nil h_ne⟩).2 := by
      simp [List.head_eq_getElem]
    rw [h_head, ← heq]
    exact lgvPath_y_nondecreasing vertices h_arcs 0 i (List.length_pos_of_ne_nil h_ne) hi (Nat.zero_le _)
  · -- y ≤ getLast.2
    have h_last : (vertices.getLast h_ne).2 =
        (vertices.get ⟨vertices.length - 1, Nat.sub_lt (List.length_pos_of_ne_nil h_ne) Nat.one_pos⟩).2 := by
      simp [List.getLast_eq_getElem]
    rw [h_last, ← heq]
    have hlen : vertices.length - 1 < vertices.length := Nat.sub_lt (List.length_pos_of_ne_nil h_ne) Nat.one_pos
    have hi_le : i ≤ vertices.length - 1 := by omega
    exact lgvPath_y_nondecreasing vertices h_arcs i (vertices.length - 1) hi hlen hi_le

/-- Auxiliary lemma: the k-th element of lgvPathEastStepYCoords corresponds to a vertex
    at x-coordinate start_x + k, AND that vertex is the start of an east step.
    This is the core induction for lgvPathEastStepYCoords_at_x. -/
theorem lgvPathEastStepYCoords_at_x_aux (vertices : List (ℤ × ℤ))
    (h_ne : vertices ≠ [])
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩))
    (k : ℕ) (hk : k < (lgvPathEastStepYCoords vertices).length) :
    ∃ (idx : ℕ) (hidx : idx < vertices.length),
      (vertices.get ⟨idx, hidx⟩).1 = (vertices.head h_ne).1 + k ∧
      (vertices.get ⟨idx, hidx⟩).2 = (lgvPathEastStepYCoords vertices)[k] ∧
      (∀ hidx_next : idx + 1 < vertices.length,
        (vertices.get ⟨idx + 1, hidx_next⟩).1 = (vertices.get ⟨idx, hidx⟩).1 + 1 ∧
        (vertices.get ⟨idx + 1, hidx_next⟩).2 = (vertices.get ⟨idx, hidx⟩).2) := by
  induction vertices generalizing k with
  | nil => simp [lgvPathEastStepYCoords] at hk
  | cons v₀ tl ih =>
    cases tl with
    | nil => simp [lgvPathEastStepYCoords] at hk
    | cons v₁ rest =>
      simp only [lgvPathEastStepYCoords] at hk ⊢
      have h_arcs' : ∀ j : ℕ, ∀ hj : j + 1 < (v₁ :: rest).length,
          LGV.integerLattice.arc ((v₁ :: rest).get ⟨j, Nat.lt_of_succ_lt hj⟩)
            ((v₁ :: rest).get ⟨j + 1, hj⟩) := by
        intro j hj
        have hj' : (j + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hj ⊢; omega
        have := h_arcs (j + 1) hj'
        simp at this ⊢; exact this
      have h_ne' : v₁ :: rest ≠ [] := List.cons_ne_nil _ _
      have harc := h_arcs 0 (by simp : 0 + 1 < (v₀ :: v₁ :: rest).length)
      simp at harc
      simp only [LGV.integerLattice] at harc
      split_ifs at hk ⊢ with h_east
      · -- v₀ → v₁ is an east step
        obtain ⟨heast_x, heast_y⟩ := h_east
        cases k with
        | zero =>
          -- The 0th element is v₀.2, and x = start_x + 0 = v₀.1
          refine ⟨0, by simp, ?_, ?_, ?_⟩
          · simp [List.head_cons]
          · rfl
          · intro hidx_next
            simp only [List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ]
            exact ⟨heast_x, heast_y⟩
        | succ k' =>
          -- Use IH on the tail
          simp at hk
          have ih' := ih h_ne' h_arcs' k' hk
          obtain ⟨idx, hidx, hx, hy, heast_step⟩ := ih'
          simp only [List.get_eq_getElem, List.head_cons] at hx
          have hidx' : idx + 1 < (v₀ :: v₁ :: rest).length := by
            simp only [List.length_cons] at hidx ⊢; omega
          refine ⟨idx + 1, hidx', ?_, ?_, ?_⟩
          · simp only [List.get_eq_getElem, List.head_cons]
            have heq : (v₀ :: v₁ :: rest)[idx + 1]'hidx' = (v₁ :: rest)[idx]'hidx := by simp
            rw [heq, hx]
            omega
          · simp only [List.get_eq_getElem] at hy ⊢
            have heq : (v₀ :: v₁ :: rest)[idx + 1]'hidx' = (v₁ :: rest)[idx]'hidx := by simp
            rw [heq, hy]
            simp [List.getElem_cons_succ]
          · intro hidx_next
            have hidx_tail : idx + 1 < (v₁ :: rest).length := by simp at hidx_next hidx ⊢; omega
            have heast_tail := heast_step hidx_tail
            simp only [List.get_eq_getElem] at heast_tail ⊢
            constructor
            · have h1 : (v₀ :: v₁ :: rest)[idx + 1 + 1]'hidx_next = (v₁ :: rest)[idx + 1]'hidx_tail := by simp
              have h2 : (v₀ :: v₁ :: rest)[idx + 1]'(Nat.lt_of_succ_lt hidx_next) = (v₁ :: rest)[idx]'hidx := by simp
              rw [h1, h2]; exact heast_tail.1
            · have h1 : (v₀ :: v₁ :: rest)[idx + 1 + 1]'hidx_next = (v₁ :: rest)[idx + 1]'hidx_tail := by simp
              have h2 : (v₀ :: v₁ :: rest)[idx + 1]'(Nat.lt_of_succ_lt hidx_next) = (v₁ :: rest)[idx]'hidx := by simp
              rw [h1, h2]; exact heast_tail.2
      · -- v₀ → v₁ is a north step
        -- The list is just lgvPathEastStepYCoords (v₁ :: rest)
        -- Use IH
        have ih' := ih h_ne' h_arcs' k hk
        obtain ⟨idx, hidx, hx, hy, heast_step⟩ := ih'
        simp only [List.get_eq_getElem, List.head_cons] at hx
        have hidx' : idx + 1 < (v₀ :: v₁ :: rest).length := by
          simp only [List.length_cons] at hidx ⊢; omega
        refine ⟨idx + 1, hidx', ?_, ?_, ?_⟩
        · simp only [List.get_eq_getElem, List.head_cons]
          have heq : (v₀ :: v₁ :: rest)[idx + 1]'hidx' = (v₁ :: rest)[idx]'hidx := by simp
          rw [heq, hx]
          -- v₁.1 = v₀.1 from north step
          rcases harc with ⟨hx', hy'⟩ | ⟨hx', _⟩
          · -- East step, but h_east says not
            simp at h_east
            have hne : v₁.2 ≠ v₀.2 := h_east hx'
            exact absurd hy' hne
          · omega
        · simp only [List.get_eq_getElem] at hy ⊢
          have heq : (v₀ :: v₁ :: rest)[idx + 1]'hidx' = (v₁ :: rest)[idx]'hidx := by simp
          rw [heq, hy]
        · intro hidx_next
          have hidx_tail : idx + 1 < (v₁ :: rest).length := by simp at hidx_next hidx ⊢; omega
          have heast_tail := heast_step hidx_tail
          simp only [List.get_eq_getElem] at heast_tail ⊢
          constructor
          · have h1 : (v₀ :: v₁ :: rest)[idx + 1 + 1]'hidx_next = (v₁ :: rest)[idx + 1]'hidx_tail := by simp
            have h2 : (v₀ :: v₁ :: rest)[idx + 1]'(Nat.lt_of_succ_lt hidx_next) = (v₁ :: rest)[idx]'hidx := by simp
            rw [h1, h2]; exact heast_tail.1
          · have h1 : (v₀ :: v₁ :: rest)[idx + 1 + 1]'hidx_next = (v₁ :: rest)[idx + 1]'hidx_tail := by simp
            have h2 : (v₀ :: v₁ :: rest)[idx + 1]'(Nat.lt_of_succ_lt hidx_next) = (v₁ :: rest)[idx]'hidx := by simp
            rw [h1, h2]; exact heast_tail.2

/-- The k-th east-step y-coordinate equals the y-coordinate at x = start_x + k.

    This lemma establishes that `lgvPathEastStepYCoords[k]` is the y-coordinate of the
    path at x-coordinate start_x + k, where start_x is the x-coordinate of the first vertex.

    The k-th east step occurs at x = start_x + k because:
    - The path starts at x = start_x
    - Each east step increases x by 1
    - The k-th east step is preceded by exactly k east steps (indices 0, 1, ..., k-1)
    - So the k-th east step starts at x = start_x + k -/
theorem lgvPathEastStepYCoords_at_x (p : LGV.SimpleDigraph.Path LGV.integerLattice)
    (k : ℕ) (hk : k < (lgvPathEastStepYCoords p.vertices).length) :
    ∃ (idx : ℕ) (hidx : idx < p.vertices.length),
      (p.vertices.get ⟨idx, hidx⟩).1 = p.start.1 + k ∧
      (p.vertices.get ⟨idx, hidx⟩).2 = (lgvPathEastStepYCoords p.vertices)[k] := by
  have h := lgvPathEastStepYCoords_at_x_aux p.vertices p.nonempty p.arcs_valid k hk
  obtain ⟨idx, hidx, hx, hy, _⟩ := h
  refine ⟨idx, hidx, ?_, hy⟩
  simp only [LGV.SimpleDigraph.Path.start, List.head_eq_getElem] at hx ⊢
  convert hx using 2

/-- The index returned by lgvPathEastStepYCoords_at_x is the start of an east step.
    If idx + 1 < vertices.length, then the step from idx to idx+1 is an east step. -/
theorem lgvPathEastStepYCoords_at_x_is_east_step (p : LGV.SimpleDigraph.Path LGV.integerLattice)
    (k : ℕ) (hk : k < (lgvPathEastStepYCoords p.vertices).length)
    (idx : ℕ) (hidx : idx < p.vertices.length)
    (_hx : (p.vertices.get ⟨idx, hidx⟩).1 = p.start.1 + k)
    (hy : (p.vertices.get ⟨idx, hidx⟩).2 = (lgvPathEastStepYCoords p.vertices)[k])
    (hidx_next : idx + 1 < p.vertices.length) :
    (p.vertices.get ⟨idx + 1, hidx_next⟩).1 = (p.vertices.get ⟨idx, hidx⟩).1 + 1 ∧
    (p.vertices.get ⟨idx + 1, hidx_next⟩).2 = (p.vertices.get ⟨idx, hidx⟩).2 := by
  -- Use the strengthened auxiliary lemma which proves this directly
  have h := lgvPathEastStepYCoords_at_x_aux p.vertices p.nonempty p.arcs_valid k hk
  obtain ⟨idx', hidx', hx', hy', heast_step⟩ := h

  -- The step from idx to idx+1 is either east or north
  have harc := p.arcs_valid idx hidx_next
  rcases harc with ⟨heast_x, heast_y⟩ | ⟨hnorth_x, hnorth_y⟩
  · -- East step: this is what we want to prove
    constructor
    · have h1 : (p.vertices.get ⟨idx, Nat.lt_of_succ_lt hidx_next⟩).1 =
                (p.vertices.get ⟨idx, hidx⟩).1 := rfl
      rw [← h1]; exact heast_x
    · have h1 : (p.vertices.get ⟨idx, Nat.lt_of_succ_lt hidx_next⟩).2 =
                (p.vertices.get ⟨idx, hidx⟩).2 := rfl
      rw [← h1]; exact heast_y
  · -- North step: contradiction
    -- We show idx = idx' using the fact that the path has no duplicate vertices
    -- (since integer lattice is acyclic)

    -- First, show that the vertices at idx and idx' are equal
    have hv_eq : p.vertices.get ⟨idx, hidx⟩ = p.vertices.get ⟨idx', hidx'⟩ := by
      ext
      · -- x-coordinates equal: both are start.x + k
        simp only [LGV.SimpleDigraph.Path.start, List.head_eq_getElem] at _hx hx'
        have hlen : 0 < p.vertices.length := List.length_pos_of_ne_nil p.nonempty
        have hx1 : (p.vertices.get ⟨idx, hidx⟩).1 = (p.vertices[0]'hlen).1 + k := _hx
        have hx2 : (p.vertices.get ⟨idx', hidx'⟩).1 = (p.vertices[0]'hlen).1 + k := by
          simp only [List.get_eq_getElem] at hx' ⊢
          convert hx' using 2
        omega
      · -- y-coordinates equal: both are ycoords[k]
        rw [hy, hy']

    -- The path has no duplicate vertices (since integer lattice is acyclic)
    have hnodup := LGV.SimpleDigraph.Path.vertices_nodup_of_acyclic LGV.integerLattice_acyclic p
    rw [List.nodup_iff_injective_getElem] at hnodup

    -- Since vertices at idx and idx' are equal, idx = idx'
    have hidx_eq : idx = idx' := by
      have hinj := @hnodup ⟨idx, hidx⟩ ⟨idx', hidx'⟩
      simp only [Fin.mk.injEq] at hinj
      simp only [List.get_eq_getElem] at hv_eq
      exact hinj hv_eq

    -- Now use the east step property from the aux lemma
    -- The east step property says: step from idx' to idx'+1 is east (x+1, y same)
    -- But hnorth_x says: step from idx to idx+1 has x unchanged
    -- Since idx = idx', this is a contradiction

    have hidx_next' : idx' + 1 < p.vertices.length := by rw [← hidx_eq]; exact hidx_next
    have heast := heast_step hidx_next'
    simp only [List.get_eq_getElem] at heast

    -- heast.1 says x(idx'+1) = x(idx') + 1
    -- hnorth_x says x(idx+1) = x(idx)
    -- Since idx = idx', we have x(idx'+1) = x(idx') and x(idx'+1) = x(idx') + 1
    -- This gives 0 = 1, contradiction

    have hx_east : p.vertices[idx' + 1].1 = p.vertices[idx'].1 + 1 := heast.1
    have hx_north : p.vertices[idx + 1].1 = p.vertices[idx].1 := by
      have := hnorth_x
      simp only [List.get_eq_getElem] at this
      exact this
    -- Substitute idx = idx' into hx_north
    subst hidx_eq
    -- Now hx_north : p.vertices[idx' + 1].1 = p.vertices[idx'].1
    -- And hx_east : p.vertices[idx' + 1].1 = p.vertices[idx'].1 + 1
    -- This gives: p.vertices[idx'].1 = p.vertices[idx'].1 + 1, contradiction
    omega

/-- Helper: x-coordinate is monotone (non-decreasing) along a path in the integer lattice.
    This follows from the fact that each step is either east (x+1) or north (x unchanged). -/
theorem integerLattice_path_x_monotone (p : LGV.SimpleDigraph.Path LGV.integerLattice)
    (i j : ℕ) (hi : i < p.vertices.length) (hj : j < p.vertices.length) (hij : i ≤ j) :
    (p.vertices.get ⟨i, hi⟩).1 ≤ (p.vertices.get ⟨j, hj⟩).1 := by
  induction j with
  | zero => simp only [Nat.le_zero] at hij; subst hij; rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hik
    · rfl
    · have hk : k < p.vertices.length := Nat.lt_of_succ_lt hj
      have h1 := ih hk (Nat.lt_succ_iff.mp hik)
      have hstep := LGV.integerLattice_path_x_step p k hj
      rcases hstep with h | h <;> omega

/-- Helper: if x-coordinates differ strictly, then indices differ strictly.
    Contrapositive of x-monotonicity. -/
theorem integerLattice_path_x_lt_implies_idx_lt (p : LGV.SimpleDigraph.Path LGV.integerLattice)
    (i j : ℕ) (hi : i < p.vertices.length) (hj : j < p.vertices.length)
    (hx : (p.vertices.get ⟨i, hi⟩).1 < (p.vertices.get ⟨j, hj⟩).1) : i < j := by
  by_contra h; push Not at h
  have := integerLattice_path_x_monotone p j i hj hi h; omega

/-- Helper: at a fixed x-coordinate, the y-coordinates of vertices form a contiguous range
    starting from the first vertex at that x. 
    
    If vertex i has x = x₀ and vertex j has x = x₀ with i < j, then for any y in 
    [y_i, y_j], there exists a vertex k with i ≤ k ≤ j having (x₀, y).
    
    This follows from the fact that y changes by 0 or 1 at each step, and x stays the same
    during north steps (y increases by 1). -/
theorem integerLattice_path_y_contiguous_at_x (p : LGV.SimpleDigraph.Path LGV.integerLattice)
    (x₀ : ℤ)
    (i j : ℕ) (hi : i < p.vertices.length) (hj : j < p.vertices.length) (hij : i ≤ j)
    (hx_i : (p.vertices.get ⟨i, hi⟩).1 = x₀)
    (hx_j : (p.vertices.get ⟨j, hj⟩).1 = x₀)
    (y : ℤ) (hy_lo : (p.vertices.get ⟨i, hi⟩).2 ≤ y) (hy_hi : y ≤ (p.vertices.get ⟨j, hj⟩).2) :
    ∃ (k : ℕ) (hk : k < p.vertices.length), i ≤ k ∧ k ≤ j ∧ 
      (p.vertices.get ⟨k, hk⟩).1 = x₀ ∧ (p.vertices.get ⟨k, hk⟩).2 = y := by
  -- Use discrete IVT on y-coordinates
  -- The y-coordinate at index i is y_i, at index j is y_j, and y ∈ [y_i, y_j]
  -- Since y changes by 0 or 1 at each step, there exists k with y_k = y
  induction j generalizing y with
  | zero =>
    simp only [Nat.le_zero] at hij
    subst hij
    exact ⟨0, hi, le_refl 0, le_refl 0, hx_i, by omega⟩
  | succ j' ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hij'
    · -- i = j' + 1
      exact ⟨j' + 1, hj, le_refl _, le_refl _, hx_j, by omega⟩
    · -- i < j' + 1, so i ≤ j'
      have hj'_lt : j' < p.vertices.length := Nat.lt_of_succ_lt hj
      -- Check if x at j' equals x₀
      have hstep := LGV.integerLattice_path_x_step p j' hj
      rcases hstep with hnorth | heast
      · -- North step: x(j'+1) - x(j') = 0, so x(j'+1) = x(j')
        -- Also y(j'+1) = y(j') + 1 (north step increases y by 1)
        have hx_j'_eq : (p.vertices.get ⟨j' + 1, hj⟩).1 = (p.vertices.get ⟨j', hj'_lt⟩).1 := by
          have h1 : (p.vertices.get ⟨j' + 1, hj⟩).1 - (p.vertices.get ⟨j', Nat.lt_of_succ_lt hj⟩).1 = 0 := hnorth
          have h2 : (p.vertices.get ⟨j', Nat.lt_of_succ_lt hj⟩).1 = (p.vertices.get ⟨j', hj'_lt⟩).1 := rfl
          omega
        have hx_j' : (p.vertices.get ⟨j', hj'_lt⟩).1 = x₀ := by
          rw [hx_j] at hx_j'_eq
          exact hx_j'_eq.symm
        -- Get y-coordinate relation
        have hy_j'_eq : (p.vertices.get ⟨j' + 1, hj⟩).2 = (p.vertices.get ⟨j', hj'_lt⟩).2 + 1 := by
          have harc := p.arcs_valid j' hj
          rcases harc with ⟨hx, hy⟩ | ⟨hx, hy⟩
          · -- East step: x increases by 1, y stays same
            -- But we know x(j'+1) - x(j') = 0 from hnorth, contradiction
            have h1 : (p.vertices.get ⟨j' + 1, hj⟩).1 = (p.vertices.get ⟨j', Nat.lt_of_succ_lt hj⟩).1 + 1 := hx
            have h2 : (p.vertices.get ⟨j' + 1, hj⟩).1 - (p.vertices.get ⟨j', Nat.lt_of_succ_lt hj⟩).1 = 0 := hnorth
            omega
          · -- North step: x stays same, y increases by 1
            have h2 : (p.vertices.get ⟨j', Nat.lt_of_succ_lt hj⟩).2 = (p.vertices.get ⟨j', hj'_lt⟩).2 := rfl
            omega
        -- If y = y(j'+1), we're done
        by_cases hy_eq_j : y = (p.vertices.get ⟨j' + 1, hj⟩).2
        · exact ⟨j' + 1, hj, Nat.le_of_lt hij', le_refl _, hx_j, hy_eq_j.symm⟩
        · -- y < y(j'+1), so y ≤ y(j') = y(j'+1) - 1
          have hy_le_j' : y ≤ (p.vertices.get ⟨j', hj'_lt⟩).2 := by
            rw [hy_j'_eq] at hy_hi
            have := ne_iff_lt_or_gt.mp hy_eq_j
            rcases this with h | h
            · omega
            · omega
          -- Apply IH to find vertex at index ≤ j' with y-coordinate y
          have := ih hj'_lt (Nat.lt_succ_iff.mp hij') hx_j' y hy_lo hy_le_j'
          obtain ⟨k, hk, hik, hkj', hx_k, hy_k⟩ := this
          exact ⟨k, hk, hik, Nat.le_succ_of_le hkj', hx_k, hy_k⟩
      · -- East step: x(j'+1) - x(j') = 1, so x(j'+1) = x(j') + 1
        -- Since x(j'+1) = x₀, we have x(j') = x₀ - 1 ≠ x₀
        have hx_j'_eq : (p.vertices.get ⟨j' + 1, hj⟩).1 = (p.vertices.get ⟨j', hj'_lt⟩).1 + 1 := by
          have h1 : (p.vertices.get ⟨j' + 1, hj⟩).1 - (p.vertices.get ⟨j', Nat.lt_of_succ_lt hj⟩).1 = 1 := heast
          have h2 : (p.vertices.get ⟨j', Nat.lt_of_succ_lt hj⟩).1 = (p.vertices.get ⟨j', hj'_lt⟩).1 := rfl
          omega
        have hx_j' : (p.vertices.get ⟨j', hj'_lt⟩).1 = x₀ - 1 := by
          rw [hx_j] at hx_j'_eq
          omega
        -- If i = j', then x(i) = x₀ but x(j') = x₀ - 1, contradiction
        have hi_ne_j' : i ≠ j' := by
          intro heq
          subst heq
          rw [hx_i] at hx_j'
          omega
        -- So i < j'
        have hi_lt_j' : i < j' := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hij') hi_ne_j'
        -- x is non-decreasing, so x(i) ≤ x(j')
        have hx_i_le : (p.vertices.get ⟨i, hi⟩).1 ≤ (p.vertices.get ⟨j', hj'_lt⟩).1 := 
          integerLattice_path_x_monotone p i j' hi hj'_lt (Nat.le_of_lt hi_lt_j')
        -- But x(i) = x₀ and x(j') = x₀ - 1 < x₀, contradiction
        rw [hx_i, hx_j'] at hx_i_le
        omega

/-- Key lemma: for two non-intersecting paths, if one is above the other at some x-coordinate,
    it stays above at all greater x-coordinates where both paths have vertices.

    This is the "paths don't cross" property for x-coordinates.
    The proof uses discrete IVT: if the y-difference ever becomes ≤ 0, there must be
    a point where it equals 0, meaning the paths share a vertex (contradiction). -/
theorem paths_above_at_x_stays_above (p p' : LGV.SimpleDigraph.Path LGV.integerLattice)
    (hni : ∀ v, v ∈ p.vertices → v ∉ p'.vertices)
    (x₀ : ℤ) -- x-coordinate where p' is above p
    -- Both paths have vertices at x₀
    (hx₀_p : ∃ (idx : ℕ) (hidx : idx < p.vertices.length), (p.vertices.get ⟨idx, hidx⟩).1 = x₀)
    (hx₀_p' : ∃ (idx : ℕ) (hidx : idx < p'.vertices.length), (p'.vertices.get ⟨idx, hidx⟩).1 = x₀)
    -- p' is strictly above p at x₀
    (h_above : ∀ (idx_p : ℕ) (hidx_p : idx_p < p.vertices.length)
               (idx_p' : ℕ) (hidx_p' : idx_p' < p'.vertices.length),
               (p.vertices.get ⟨idx_p, hidx_p⟩).1 = x₀ →
               (p'.vertices.get ⟨idx_p', hidx_p'⟩).1 = x₀ →
               (p'.vertices.get ⟨idx_p', hidx_p'⟩).2 > (p.vertices.get ⟨idx_p, hidx_p⟩).2)
    -- A greater x-coordinate x₁
    (x₁ : ℤ) (hx₁ : x₁ ≥ x₀)
    -- Both paths have vertices at x₁
    (hx₁_p : ∃ (idx : ℕ) (hidx : idx < p.vertices.length), (p.vertices.get ⟨idx, hidx⟩).1 = x₁)
    (hx₁_p' : ∃ (idx : ℕ) (hidx : idx < p'.vertices.length), (p'.vertices.get ⟨idx, hidx⟩).1 = x₁) :
    ∀ (idx_p : ℕ) (hidx_p : idx_p < p.vertices.length)
      (idx_p' : ℕ) (hidx_p' : idx_p' < p'.vertices.length),
      (p.vertices.get ⟨idx_p, hidx_p⟩).1 = x₁ →
      (p'.vertices.get ⟨idx_p', hidx_p'⟩).1 = x₁ →
      (p'.vertices.get ⟨idx_p', hidx_p'⟩).2 > (p.vertices.get ⟨idx_p, hidx_p⟩).2 := by
  -- The proof uses discrete IVT on the y-difference.
  -- If p' drops to or below p at some x > x₀, there must be a crossing point.
  intro idx_p hidx_p idx_p' hidx_p' hx_p hx_p'
  by_contra h_not_above
  push Not at h_not_above
  -- Get witnesses for x₀
  obtain ⟨idx₀_p, hidx₀_p, hx₀_p_eq⟩ := hx₀_p
  obtain ⟨idx₀_p', hidx₀_p', hx₀_p'_eq⟩ := hx₀_p'
  -- At x₀, p' is strictly above p
  have h_above_at_x₀ := h_above idx₀_p hidx₀_p idx₀_p' hidx₀_p' hx₀_p_eq hx₀_p'_eq
  -- Define y-coordinate at x for each path (using the unique vertex at that x)
  -- The key insight: at x₁, if y_p' ≤ y_p, then by discrete IVT on x-coordinates,
  -- there exists some x ∈ [x₀, x₁] where y_p' = y_p, meaning paths share a vertex.
  --
  -- Use the sum-based approach: at x₀, sum_p = x₀ + y_p, sum_p' = x₀ + y_p'
  -- Since y_p' > y_p at x₀, sum_p' > sum_p.
  -- At x₁, if y_p' ≤ y_p, then sum_p' ≤ sum_p.
  -- By discrete IVT on sums, there's a sum s where both paths have the same y.
  -- Since x + y = s for both, and y is the same, x is the same.
  -- So paths share a vertex, contradiction.
  let y_p_x₀ := (p.vertices.get ⟨idx₀_p, hidx₀_p⟩).2
  let y_p'_x₀ := (p'.vertices.get ⟨idx₀_p', hidx₀_p'⟩).2
  let y_p_x₁ := (p.vertices.get ⟨idx_p, hidx_p⟩).2
  let y_p'_x₁ := (p'.vertices.get ⟨idx_p', hidx_p'⟩).2
  -- Sums at x₀ and x₁
  let s_p_x₀ := x₀ + y_p_x₀
  let s_p'_x₀ := x₀ + y_p'_x₀
  let s_p_x₁ := x₁ + y_p_x₁
  let s_p'_x₁ := x₁ + y_p'_x₁
  -- At x₀: s_p'_x₀ > s_p_x₀ (since y_p'_x₀ > y_p_x₀)
  have hs₀ : s_p'_x₀ > s_p_x₀ := by simp only [s_p'_x₀, s_p_x₀]; omega
  -- At x₁: s_p'_x₁ ≤ s_p_x₁ (since y_p'_x₁ ≤ y_p_x₁ and both have x = x₁)
  have hs₁ : s_p'_x₁ ≤ s_p_x₁ := by simp only [s_p'_x₁, s_p_x₁]; omega
  -- The sums at vertices are determined by their index
  have hsum_p_x₀ := LGV.integerLattice_path_vertex_sum p idx₀_p hidx₀_p
  have hsum_p'_x₀ := LGV.integerLattice_path_vertex_sum p' idx₀_p' hidx₀_p'
  have hsum_p_x₁ := LGV.integerLattice_path_vertex_sum p idx_p hidx_p
  have hsum_p'_x₁ := LGV.integerLattice_path_vertex_sum p' idx_p' hidx_p'
  -- Case split: x₁ = x₀ or x₁ > x₀
  rcases eq_or_lt_of_le hx₁ with hx_eq | hx_gt
  · -- Case x₁ = x₀: contradiction with h_above and h_not_above
    subst hx_eq
    have := h_above idx_p hidx_p idx_p' hidx_p' hx_p hx_p'
    omega
  · -- Case x₁ > x₀: use discrete IVT
    -- Define the y-difference function on sum values
    let y_p_fn (s : ℤ) : ℤ :=
      let idx := (s - p.start.1 - p.start.2).toNat
      if h : idx < p.vertices.length then (p.vertices.get ⟨idx, h⟩).2 else 0
    let y_p'_fn (s : ℤ) : ℤ :=
      let idx := (s - p'.start.1 - p'.start.2).toNat
      if h : idx < p'.vertices.length then (p'.vertices.get ⟨idx, h⟩).2 else 0
    let diff (s : ℤ) : ℤ := y_p'_fn s - y_p_fn s
    -- The key constraint: idx₀_p' < idx_p' (since x strictly increases from x₀ to x₁)
    have hidx_p'_mono : idx₀_p' < idx_p' := by
      have := integerLattice_path_x_lt_implies_idx_lt p' idx₀_p' idx_p' hidx₀_p' hidx_p'
      simp only [hx₀_p'_eq, hx_p'] at this
      exact this hx_gt
    -- Similarly for p: idx₀_p < idx_p
    have hidx_p_mono : idx₀_p < idx_p := by
      have := integerLattice_path_x_lt_implies_idx_lt p idx₀_p idx_p hidx₀_p hidx_p
      simp only [hx₀_p_eq, hx_p] at this
      exact this hx_gt
    -- The sum range for p' from x₀ to x₁ is [s_p'_x₀, s_p'_x₁]
    -- Since s_p'_x₁ ≤ s_p_x₁ and s_p'_x₀ < s_p'_x₁, we have s_p'_x₀ ≤ s_p_x₁
    have hs_p'_x₀_lt_sp'x₁ : s_p'_x₀ < s_p'_x₁ := by
      simp only [s_p'_x₀, s_p'_x₁]; omega
    have hs_p'_x₀_le_spx₁ : s_p'_x₀ ≤ s_p_x₁ := le_trans (le_of_lt hs_p'_x₀_lt_sp'x₁) hs₁
    -- Index bounds for the overlapping sum range
    have hidx_p_sp'x₀ : (s_p'_x₀ - p.start.1 - p.start.2).toNat < p.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p
      simp only [s_p'_x₀, s_p_x₀, s_p_x₁] at hs₀ hs_p'_x₀_le_spx₁; omega
    have hidx_p'_sp'x₀ : (s_p'_x₀ - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p'
      simp only [s_p'_x₀]; omega
    have hidx_p_sp'x₁ : (s_p'_x₁ - p.start.1 - p.start.2).toNat < p.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p
      simp only [s_p'_x₁, s_p_x₁] at hs₁; omega
    have hidx_p'_sp'x₁ : (s_p'_x₁ - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p'
      simp only [s_p'_x₁]; omega
    -- At s_p'_x₀, the index in p' is idx₀_p'
    have heq_idx_p'_sp'x₀ : (s_p'_x₀ - p'.start.1 - p'.start.2).toNat = idx₀_p' := by
      simp only [s_p'_x₀]; omega
    -- At s_p'_x₁, the index in p' is idx_p'
    have heq_idx_p'_sp'x₁ : (s_p'_x₁ - p'.start.1 - p'.start.2).toNat = idx_p' := by
      simp only [s_p'_x₁]; omega
    -- At s_p'_x₀, the x-coordinate of p is ≥ x₀
    have hx_p_at_sp'x₀ : (p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩).1 ≥ x₀ := by
      have hidx_ge : (s_p'_x₀ - p.start.1 - p.start.2).toNat ≥ idx₀_p := by
        simp only [s_p'_x₀, s_p_x₀] at hs₀; omega
      have := integerLattice_path_x_monotone p idx₀_p (s_p'_x₀ - p.start.1 - p.start.2).toNat
        hidx₀_p hidx_p_sp'x₀ hidx_ge
      omega
    -- At s_p'_x₀, y_p' > y_p (or they share a vertex, contradiction)
    have hdiff_sp'x₀ : diff s_p'_x₀ > 0 := by
      simp only [diff, y_p_fn, y_p'_fn, hidx_p_sp'x₀, hidx_p'_sp'x₀, dite_true]
      by_contra h_le
      push Not at h_le
      have hsum_p_at_sp'x₀ := LGV.integerLattice_path_vertex_sum p
        (s_p'_x₀ - p.start.1 - p.start.2).toNat hidx_p_sp'x₀
      have hy_p'_val : (p'.vertices.get ⟨(s_p'_x₀ - p'.start.1 - p'.start.2).toNat, hidx_p'_sp'x₀⟩).2 = y_p'_x₀ := by
        have : (s_p'_x₀ - p'.start.1 - p'.start.2).toNat = idx₀_p' := heq_idx_p'_sp'x₀
        simp only [List.get_eq_getElem, y_p'_x₀, this]
      have heq_y : (p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩).2 = y_p'_x₀ := by
        simp only [hy_p'_val] at h_le
        have hsum : (p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩).1 +
               (p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩).2 = s_p'_x₀ := by
          simp only [s_p'_x₀] at hsum_p_at_sp'x₀ ⊢; omega
        omega
      have heq_x : (p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩).1 = x₀ := by
        have hsum : (p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩).1 +
               (p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩).2 = s_p'_x₀ := by
          simp only [s_p'_x₀] at hsum_p_at_sp'x₀ ⊢; omega
        omega
      have hv_eq : p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩ =
                   p'.vertices.get ⟨idx₀_p', hidx₀_p'⟩ := by
        apply Prod.ext
        · simp only [heq_x, hx₀_p'_eq]
        · simp only [heq_y]; rfl
      have hmem_p : p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩ ∈ p.vertices :=
        List.get_mem p.vertices ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩
      have hmem_p' : p'.vertices.get ⟨idx₀_p', hidx₀_p'⟩ ∈ p'.vertices :=
        List.get_mem p'.vertices ⟨idx₀_p', hidx₀_p'⟩
      rw [hv_eq] at hmem_p
      exact hni _ hmem_p hmem_p'
    -- At s_p'_x₁, diff ≤ 0
    have hdiff_sp'x₁ : diff s_p'_x₁ ≤ 0 := by
      simp only [diff, y_p_fn, y_p'_fn, hidx_p_sp'x₁, hidx_p'_sp'x₁, dite_true]
      have hy_p'_val : (p'.vertices.get ⟨(s_p'_x₁ - p'.start.1 - p'.start.2).toNat, hidx_p'_sp'x₁⟩).2 = y_p'_x₁ := by
        have : (s_p'_x₁ - p'.start.1 - p'.start.2).toNat = idx_p' := heq_idx_p'_sp'x₁
        simp only [List.get_eq_getElem, y_p'_x₁, this]
      have hsum_p_at_sp'x₁ := LGV.integerLattice_path_vertex_sum p
        (s_p'_x₁ - p.start.1 - p.start.2).toNat hidx_p_sp'x₁
      have hx_p_le : (p.vertices.get ⟨(s_p'_x₁ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₁⟩).1 ≤ x₁ := by
        have hidx_le : (s_p'_x₁ - p.start.1 - p.start.2).toNat ≤ idx_p := by
          simp only [s_p'_x₁, s_p_x₁] at hs₁; omega
        have := integerLattice_path_x_monotone p (s_p'_x₁ - p.start.1 - p.start.2).toNat idx_p
          hidx_p_sp'x₁ hidx_p hidx_le
        omega
      simp only [hy_p'_val]
      have hsum : (p.vertices.get ⟨(s_p'_x₁ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₁⟩).1 +
             (p.vertices.get ⟨(s_p'_x₁ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₁⟩).2 = s_p'_x₁ := by
        simp only [s_p'_x₁] at hsum_p_at_sp'x₁ ⊢; omega
      omega
    -- The difference function changes by at most 1 at each step
    have hdiff_step : ∀ s : ℤ, s_p'_x₀ ≤ s → s < s_p'_x₁ → |diff (s + 1) - diff s| ≤ 1 := by
      intro s hs_lo hs_hi
      simp only [diff, y_p_fn, y_p'_fn]
      have hs_p_lo : s ≥ p.start.1 + p.start.2 := by
        simp only [s_p'_x₀, s_p_x₀] at hs_lo hs₀; omega
      have hs_p_hi : s < p.finish.1 + p.finish.2 := by
        have hlen := LGV.integerLattice_path_length_eq p
        simp only [s_p'_x₁, s_p_x₁] at hs_hi hs₁; omega
      have hs_p'_lo : s ≥ p'.start.1 + p'.start.2 := by
        simp only [s_p'_x₀] at hs_lo; omega
      have hs_p'_hi : s < p'.finish.1 + p'.finish.2 := by
        have hlen := LGV.integerLattice_path_length_eq p'
        simp only [s_p'_x₁] at hs_hi; omega
      have hidx_p_s : (s - p.start.1 - p.start.2).toNat < p.vertices.length := by
        have hlen := LGV.integerLattice_path_length_eq p; omega
      have hidx_p'_s : (s - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
        have hlen := LGV.integerLattice_path_length_eq p'; omega
      have hidx_p_s1 : (s + 1 - p.start.1 - p.start.2).toNat < p.vertices.length := by
        have hlen := LGV.integerLattice_path_length_eq p; omega
      have hidx_p'_s1 : (s + 1 - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
        have hlen := LGV.integerLattice_path_length_eq p'; omega
      simp only [hidx_p_s, hidx_p'_s, hidx_p_s1, hidx_p'_s1, dite_true]
      have heq_idx_p : (s + 1 - p.start.1 - p.start.2).toNat = (s - p.start.1 - p.start.2).toNat + 1 := by omega
      have heq_idx_p' : (s + 1 - p'.start.1 - p'.start.2).toNat = (s - p'.start.1 - p'.start.2).toNat + 1 := by omega
      have hstep_p_idx : (s - p.start.1 - p.start.2).toNat + 1 < p.vertices.length := by omega
      have hstep_p'_idx : (s - p'.start.1 - p'.start.2).toNat + 1 < p'.vertices.length := by omega
      have harc_p := p.arcs_valid (s - p.start.1 - p.start.2).toNat hstep_p_idx
      have harc_p' := p'.arcs_valid (s - p'.start.1 - p'.start.2).toNat hstep_p'_idx
      rcases harc_p with ⟨_, hy_p⟩ | ⟨_, hy_p⟩ <;>
      rcases harc_p' with ⟨_, hy_p'⟩ | ⟨_, hy_p'⟩ <;>
      · simp only [heq_idx_p, heq_idx_p', abs_le]
        constructor <;> omega
    -- Apply discrete IVT
    obtain ⟨s_eq, hs_eq_lo, hs_eq_hi, hdiff_eq⟩ := LGV.discrete_ivt (le_of_lt hs_p'_x₀_lt_sp'x₁) diff
      hdiff_step (le_of_lt hdiff_sp'x₀) hdiff_sp'x₁
    -- At s_eq, both paths have the same y-coordinate
    have hidx_p_seq : (s_eq - p.start.1 - p.start.2).toNat < p.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p
      simp only [s_p'_x₀, s_p_x₀, s_p'_x₁, s_p_x₁] at hs_eq_lo hs_eq_hi hs₀ hs₁; omega
    have hidx_p'_seq : (s_eq - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p'
      simp only [s_p'_x₀, s_p'_x₁] at hs_eq_lo hs_eq_hi; omega
    simp only [diff, y_p_fn, y_p'_fn, hidx_p_seq, hidx_p'_seq, dite_true, sub_eq_zero] at hdiff_eq
    -- Both paths have the same sum value at s_eq
    have hsum_p_seq := LGV.integerLattice_path_vertex_sum p (s_eq - p.start.1 - p.start.2).toNat hidx_p_seq
    have hsum_p'_seq := LGV.integerLattice_path_vertex_sum p' (s_eq - p'.start.1 - p'.start.2).toNat hidx_p'_seq
    -- Since x + y = s_eq for both, and y_p = y_p', we have x_p = x_p'
    have hx_eq : (p.vertices.get ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩).1 =
                 (p'.vertices.get ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩).1 := by omega
    have hy_eq : (p.vertices.get ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩).2 =
                 (p'.vertices.get ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩).2 := by omega
    -- The vertices are equal
    have hv_eq : p.vertices.get ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩ =
                 p'.vertices.get ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩ :=
      Prod.ext hx_eq hy_eq
    -- This contradicts non-intersection
    have hmem_p : p.vertices.get ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩ ∈ p.vertices :=
      List.get_mem p.vertices ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩
    have hmem_p' : p'.vertices.get ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩ ∈ p'.vertices :=
      List.get_mem p'.vertices ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩
    rw [hv_eq] at hmem_p
    exact hni _ hmem_p hmem_p'
/-!
### LGV Path to LatticePath Bijection

We now construct the explicit bijection between LGV paths from (a, 1) to (c, N) and
our `LatticePath a c` type. This is needed for `lgv_pathWeightSum_eq_hsymmExt`.

The bijection:
- **LGV Path → LatticePath**: Extract east-step y-coordinates using `lgvPathEastStepYCoords`,
  then convert from ℤ (in range [1, N]) to Fin N by subtracting 1.
- **LatticePath → LGV Path**: Given a weakly increasing list of Fin N, construct the unique
  path that makes east-steps at the specified heights.

Weight preservation follows from the definition of `jacobiTrudiArcWeight`:
- East-step at y-coordinate y gets weight X_{y-1}
- North-steps get weight 1
- This matches `LatticePath.weight = ∏ h ∈ eastStepHeights, X_h`
-/


/-- Convert east-step y-coordinates (in ℤ, range [1, N]) to Fin N elements.
    This is a helper for the LGV path to LatticePath bijection. -/
def lgvYCoordsToFinN (ycoords : List ℤ) (h : ∀ y ∈ ycoords, 1 ≤ y ∧ y ≤ N) : List (Fin N) :=
  ycoords.pmap (fun y hy => ⟨(y - 1).toNat, by have := h y hy; omega⟩) (fun y hy => hy)

/-- The length of lgvYCoordsToFinN equals the length of the input list. -/
theorem lgvYCoordsToFinN_length (ycoords : List ℤ) (h : ∀ y ∈ ycoords, 1 ≤ y ∧ y ≤ N) :
    (lgvYCoordsToFinN ycoords h).length = ycoords.length := by
  simp [lgvYCoordsToFinN, List.length_pmap]

/-- The converted list preserves the chain property (weakly increasing). -/
theorem lgvYCoordsToFinN_isChain (ycoords : List ℤ) (h : ∀ y ∈ ycoords, 1 ≤ y ∧ y ≤ N)
    (hchain : ycoords.IsChain (· ≤ ·)) :
    (lgvYCoordsToFinN ycoords h).IsChain (· ≤ ·) := by
  unfold lgvYCoordsToFinN
  -- Convert to Pairwise form which is easier to work with for pmap
  rw [List.isChain_iff_pairwise] at hchain ⊢
  apply List.Pairwise.pmap hchain
  intro a ha b hb hab
  simp only [Fin.le_def]
  have ha' := h a ha
  have hb' := h b hb
  omega

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

/-- Key lemma: Non-intersection of LGV paths implies column-strictness of the converted paths.

    This is the fundamental connection between the two representations:
    - LGV: paths don't share any vertex (isNonIntersecting)
    - Nipat: paths satisfy column-strictness (colStrictPaths)

    The proof uses the fact that for sorted source/target vertices:
    - If paths i < j share a vertex (x, y), they would have the same height at some column
    - This violates column-strictness which requires strict ordering

    **Proof sketch:**
    Suppose paths i and j (with i < j) share a vertex (x, y).
    - Path i goes from (μᵢ - i, 1) to (λᵢ - i, N)
    - Path j goes from (μⱼ - j, 1) to (λⱼ - j, N)
    - At x-coordinate x, both paths have y-coordinate y
    - The east-step at column k in path i (where μᵢ - i + k = x) has height y
    - The east-step at column k' in path j (where μⱼ - j + k' = x) has height y
    - If μᵢ + k = μⱼ + k' (same tableau column), then heights should be strictly ordered
    - But both have height y, contradiction -/
theorem isNonIntersecting_implies_colStrictPaths (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i)
    (pt : LGV.PathTuple LGV.integerLattice N
      (jacobiTrudiSourceVertex mu) (jacobiTrudiTargetVertex lam))
    (hni : pt.isNonIntersecting) :
    ∀ i j : Fin N, i < j →
      ∀ k : ℕ, ∀ hk : k < ((pathTupleToLatticePaths lam mu pt) i).eastStepHeights.length,
      ∀ k' : ℕ, ∀ hk' : k' < ((pathTupleToLatticePaths lam mu pt) j).eastStepHeights.length,
      mu i + k = mu j + k' →
      ((pathTupleToLatticePaths lam mu pt) i).eastStepHeights[k] <
        ((pathTupleToLatticePaths lam mu pt) j).eastStepHeights[k'] := by
  -- The proof uses strong induction on j - i.
  -- For any i < j, we show h_i[k] < h_j[k'] when mu i + k = mu j + k'.
  --
  -- Base case (j = i + 1): We show that if h_i[k] ≥ h_j[k'], paths share a vertex.
  -- The key insight is that at x = (μ_i - i) + k - 1 = (μ_j - j) + k',
  -- path i is at y = h_i[k].val + 1 and path j is at y = h_j[k'].val + 1.
  -- If h_i[k] ≥ h_j[k'], then path i's y ≥ path j's y at this x-coordinate.
  -- But path j starts to the left of path i (at y = 1), so if they don't share
  -- a vertex, path j must be strictly above path i at all shared x-coordinates.
  -- This would force h_j[k'] > h_i[k], contradiction.
  --
  -- Inductive case (j > i + 1): Use transitivity through l = i + 1.
  intro i j hij k hk k' hk' hcol
  -- Use strong induction on the difference j - i
  have h_diff_pos : 0 < j.val - i.val := Nat.sub_pos_of_lt hij
  obtain ⟨d, hd⟩ : ∃ d, j.val - i.val = d + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_diff_pos)
  induction d using Nat.strong_induction_on generalizing i j k k' with
  | _ d ih =>
    by_cases hcons : d = 0
    · -- Base case: j = i + 1 (consecutive rows)
      subst hcons
      have hj_eq : j.val = i.val + 1 := by omega
      -- Proof by contradiction: assume h_i[k] ≥ h_j[k']
      by_contra h_not_lt
      push Not at h_not_lt
      -- We show paths share a vertex, contradicting hni
      have hij_ne : i ≠ j := Fin.ne_of_lt hij
      apply hni i j hij_ne
      -- The shared vertex is (μ_i - i, 1) - the starting point of path i.
      use ((mu i : ℤ) - (i.val : ℤ), 1)
      constructor
      · -- (μ_i - i, 1) is the start of path i
        have hstart := pt.starts i
        unfold jacobiTrudiSourceVertex jacobiTrudiSourceX at hstart
        rw [← hstart]
        exact List.head_mem (pt.paths i).nonempty
      · -- Path j visits (μ_i - i, 1)
        -- This is the key step. We need to show that path j passes through
        -- the starting point of path i.
        --
        -- The proof is by contradiction using the discrete IVT approach.
        -- We show that if path j doesn't visit (μ_i - i, 1), then h_j[k'] > h_i[k],
        -- contradicting h_not_lt.
        --
        -- Set up: path j goes from (μ_j - j, 1) to (λ_j - j, N)
        -- Since j = i + 1 and μ is weakly decreasing, μ_j - j < μ_i - i
        -- So path j starts strictly to the left of (μ_i - i, 1)
        --
        -- Key facts:
        -- 1. Path j visits x = μ_i - i (since it starts left and ends right of this x)
        -- 2. If path j doesn't visit (μ_i - i, 1), then at x = μ_i - i, path j has y > 1
        -- 3. Since paths don't share any vertex, path j stays strictly above path i
        -- 4. At x = μ_i - i + k, this means h_j[k'] > h_i[k]
        --
        -- This contradicts h_not_lt, so path j must visit (μ_i - i, 1).
        by_contra h_not_in_j
        -- Path j's start and end
        have hstart_j := pt.starts j
        have hfinish_j := pt.finishes j
        unfold jacobiTrudiSourceVertex jacobiTrudiSourceX at hstart_j
        unfold jacobiTrudiTargetVertex jacobiTrudiTargetX at hfinish_j
        -- Path j starts at (μ_j - j, 1) which is strictly left of (μ_i - i, 1)
        have hmu_j_lt : (mu j : ℤ) - (j.val : ℤ) < (mu i : ℤ) - (i.val : ℤ) := by
          have hmu_ij : mu j ≤ mu i := hmu i j (Fin.le_of_lt hij)
          omega
        -- Path j ends at x = λ_j - j. We need this to be ≥ μ_i - i + k.
        -- From hcol: mu i + k = mu j + k', and k' < lam j - mu j
        -- So mu i + k < lam j, hence μ_i - i + k < λ_j - j + 1
        have hlen_j : ((pathTupleToLatticePaths lam mu pt) j).eastStepHeights.length = lam j - mu j := by
          have h := ((pathTupleToLatticePaths lam mu pt) j).length_eq
          have hcont_j : mu j ≤ lam j := hcontained j
          simp only [sub_sub_sub_cancel_right] at h
          omega
        have hk'_bound : k' < lam j - mu j := by rw [← hlen_j]; exact hk'
        have h_col_bound : mu i + k < lam j := by omega
        -- Now we derive the contradiction from h_not_lt.
        -- The key insight is that if path j doesn't visit (μ_i - i, 1),
        -- then path j is strictly above path i at x = μ_i - i.
        -- Since paths don't intersect, path j stays above path i.
        -- At x = μ_i - i + k, this means h_j[k'] > h_i[k].
        --
        -- The east step heights satisfy:
        -- - h_i[k] is the y-coordinate (minus 1) of path i's k-th east step
        -- - h_j[k'] is the y-coordinate (minus 1) of path j's k'-th east step
        -- - Both east steps occur at the same x-coordinate
        --
        -- Since path j is above path i at x = μ_i - i, and paths don't intersect,
        -- path j stays above path i. So at x = μ_i - i + k, y_j > y_i.
        -- This means h_j[k'].val + 1 > h_i[k].val + 1, so h_j[k'] > h_i[k].
        -- But h_not_lt says h_i[k] ≥ h_j[k'], contradiction.
        have h_heights : ((pathTupleToLatticePaths lam mu pt) j).eastStepHeights[k'] >
            ((pathTupleToLatticePaths lam mu pt) i).eastStepHeights[k] := by
          -- The proof uses path_above_stays_above (the sum-based version) and
          -- lgvPathEastStepYCoords_at_x to connect eastStepHeights to actual y-coordinates.
          --
          -- Key insight: At x = μ_i - i, path i is at y = 1 (its start), while path j
          -- is at y > 1 (since it doesn't visit (μ_i - i, 1)). The sum values at these
          -- points are s_i = μ_i - i + 1 and s_j = μ_i - i + y_j > s_i.
          -- By path_above_stays_above, path j stays above path i at all later sums.
          --
          -- At x = μ_i - i + k, the east-step y-coordinates are related to the heights.
          -- By lgvPathEastStepYCoords_at_x, the y-coordinate at x = μ_i - i + k for path i
          -- is eastStepHeights[k].val + 1, and similarly for path j.
          --
          -- Since path j is above path i at x = μ_i - i, and paths don't intersect,
          -- path j stays above at x = μ_i - i + k, giving h_j[k'] > h_i[k].
          --
          -- Get the LGV paths
          let p_i := pt.paths i
          let p_j := pt.paths j
          -- Path i starts at (μ_i - i, 1)
          have hstart_i := pt.starts i
          unfold jacobiTrudiSourceVertex jacobiTrudiSourceX at hstart_i
          -- At x = μ_i - i, path i is at y = 1 (sum = μ_i - i + 1)
          -- At x = μ_i - i, path j is at y > 1 (since it doesn't visit (μ_i - i, 1))
          -- The sum for path j at x = μ_i - i is s_j = μ_i - i + y_j where y_j > 1
          -- Use path_above_stays_above with s₀ = μ_i - i + 1 (sum where path i starts)
          -- and s₁ = sum at x = μ_i - i + k
          --
          -- First, establish that path j visits x = μ_i - i at some y > 1
          have hj_visits_x₀ : ∃ (idx : ℕ) (hidx : idx < p_j.vertices.length),
              (p_j.vertices.get ⟨idx, hidx⟩).1 = (mu i : ℤ) - (i.val : ℤ) ∧
              (p_j.vertices.get ⟨idx, hidx⟩).2 > 1 := by
            -- Path j starts at (μ_j - j, 1) and ends at (λ_j - j, N)
            -- Since μ_j - j < μ_i - i < λ_j - j (from bounds), path j visits x = μ_i - i
            have hx_in_range : (mu j : ℤ) - (j.val : ℤ) < (mu i : ℤ) - (i.val : ℤ) ∧
                (mu i : ℤ) - (i.val : ℤ) ≤ (lam j : ℤ) - (j.val : ℤ) := by
              constructor
              · exact hmu_j_lt
              · have h1 : mu i + k < lam j := h_col_bound
                have h2 : k < lam i - mu i := by
                  have hlen_i : ((pathTupleToLatticePaths lam mu pt) i).eastStepHeights.length = lam i - mu i := by
                    have h := ((pathTupleToLatticePaths lam mu pt) i).length_eq
                    have hcont_i : mu i ≤ lam i := hcontained i
                    simp only [sub_sub_sub_cancel_right] at h
                    omega
                  rw [← hlen_i]; exact hk
                omega
            -- Path j is monotone in x, so it visits all x in [start.x, finish.x]
            -- Find the first vertex with x = μ_i - i
            -- This vertex has y > 1 since (μ_i - i, 1) is not in path j
            have hbd := LGV.integerLattice_path_vertices_bounded p_j
            have hlen := LGV.integerLattice_path_length_eq p_j
            rw [hstart_j, hfinish_j] at hlen hbd
            -- The x-coordinate increases from μ_j - j to λ_j - j
            -- At some index, x = μ_i - i
            -- Use that x increases by 0 or 1 at each step (integerLattice_path_x_step)
            -- Find idx such that x = μ_i - i
            -- Since start.x < μ_i - i ≤ finish.x, such idx exists
            -- The proof uses discrete IVT on x-coordinates
            --
            -- First, find an index where x = μ_i - i using discrete IVT
            -- Define x_coord(idx) = (p_j.vertices.get idx).1
            -- At idx = 0, x = μ_j - j < μ_i - i
            -- At idx = length - 1, x = λ_j - j ≥ μ_i - i
            -- x increases by 0 or 1 at each step
            -- By IVT, there exists idx with x = μ_i - i
            have hlen_pos : 0 < p_j.vertices.length := List.length_pos_of_ne_nil p_j.nonempty
            have hlast : p_j.vertices.length - 1 < p_j.vertices.length := Nat.sub_lt hlen_pos Nat.one_pos
            -- x at start < μ_i - i
            have hx_start : (p_j.vertices.get ⟨0, hlen_pos⟩).1 < (mu i : ℤ) - (i.val : ℤ) := by
              have hstart_eq : p_j.vertices.get ⟨0, hlen_pos⟩ = p_j.start := by
                simp only [LGV.SimpleDigraph.Path.start, List.head_eq_getElem, List.get_eq_getElem]
              rw [hstart_eq, hstart_j]
              exact hx_in_range.1
            -- x at end ≥ μ_i - i
            have hx_end : (p_j.vertices.get ⟨p_j.vertices.length - 1, hlast⟩).1 ≥ (mu i : ℤ) - (i.val : ℤ) := by
              have hfinish_eq : p_j.vertices.get ⟨p_j.vertices.length - 1, hlast⟩ = p_j.finish := by
                simp only [LGV.SimpleDigraph.Path.finish, List.getLast_eq_getElem, List.get_eq_getElem]
              rw [hfinish_eq, hfinish_j]
              exact hx_in_range.2
            -- Use discrete IVT to find the index
            -- The x-coordinate function: f(idx) = x(idx) - (μ_i - i)
            -- f(0) < 0 and f(length-1) ≥ 0
            -- |f(idx+1) - f(idx)| ≤ 1 (since x increases by 0 or 1)
            -- By IVT, there exists idx with f(idx) = 0
            let f (idx : ℕ) (hidx : idx < p_j.vertices.length) : ℤ :=
              (p_j.vertices.get ⟨idx, hidx⟩).1 - ((mu i : ℤ) - (i.val : ℤ))
            have hf_start : f 0 hlen_pos < 0 := by simp only [f]; omega
            have hf_end : f (p_j.vertices.length - 1) hlast ≥ 0 := by simp only [f]; omega
            -- Find the first index where f ≥ 0
            -- This index has f = 0 (since f increases by at most 1 and f(prev) < 0)
            have h_exists : ∃ (idx : ℕ) (hidx : idx < p_j.vertices.length),
                (p_j.vertices.get ⟨idx, hidx⟩).1 = (mu i : ℤ) - (i.val : ℤ) := by
              -- Use Nat.find to get the smallest index where x ≥ target
              let target : ℤ := (mu i : ℤ) - (i.val : ℤ)
              let P : ℕ → Prop := fun idx => ∃ hidx : idx < p_j.vertices.length,
                  (p_j.vertices.get ⟨idx, hidx⟩).1 ≥ target
              have hP_dec : DecidablePred P := by
                intro idx
                by_cases h : idx < p_j.vertices.length
                · exact decidable_of_iff ((p_j.vertices.get ⟨idx, h⟩).1 ≥ target)
                    ⟨fun hf => ⟨h, hf⟩, fun ⟨_, hf⟩ => hf⟩
                · exact isFalse (fun ⟨hidx, _⟩ => h hidx)
              have hP_exists : ∃ idx, P idx := ⟨p_j.vertices.length - 1, hlast, hx_end⟩
              let idx₀ := Nat.find hP_exists
              have hidx₀_lt : idx₀ < p_j.vertices.length := (Nat.find_spec hP_exists).choose
              have hx_idx₀_ge : (p_j.vertices.get ⟨idx₀, hidx₀_lt⟩).1 ≥ target :=
                (Nat.find_spec hP_exists).choose_spec
              -- Show idx₀ > 0 (since x at 0 < target)
              have hidx₀_pos : idx₀ > 0 := by
                by_contra h
                push Not at h
                have hidx₀_eq_zero : idx₀ = 0 := Nat.eq_zero_of_le_zero h
                have h1 : (p_j.vertices.get ⟨0, hlen_pos⟩).1 ≥ target := by
                  have heq' : (p_j.vertices.get ⟨idx₀, hidx₀_lt⟩).1 =
                             (p_j.vertices.get ⟨0, hlen_pos⟩).1 := by
                    simp only [hidx₀_eq_zero]
                  rw [← heq']; exact hx_idx₀_ge
                simp only [target] at h1
                omega
              -- At idx₀ - 1, x < target (by minimality of idx₀)
              have hidx₀_pred_lt : idx₀ - 1 < p_j.vertices.length :=
                Nat.lt_of_lt_of_le (Nat.sub_lt hidx₀_pos Nat.one_pos) (Nat.le_of_lt hidx₀_lt)
              have hx_pred_lt : (p_j.vertices.get ⟨idx₀ - 1, hidx₀_pred_lt⟩).1 < target := by
                by_contra h
                push Not at h
                have : P (idx₀ - 1) := ⟨hidx₀_pred_lt, h⟩
                have : idx₀ ≤ idx₀ - 1 := Nat.find_le this
                omega
              -- The step from idx₀ - 1 to idx₀ increases x by 0 or 1
              have hstep_idx : idx₀ - 1 + 1 < p_j.vertices.length := by omega
              have hstep := LGV.integerLattice_path_x_step p_j (idx₀ - 1) hstep_idx
              -- idx₀ - 1 + 1 = idx₀
              have heq : idx₀ - 1 + 1 = idx₀ := Nat.sub_add_cancel hidx₀_pos
              -- So x increases by 0 or 1 from idx₀ - 1 to idx₀
              -- Since x(idx₀ - 1) < target ≤ x(idx₀) and x increases by at most 1, x(idx₀) = target
              have hx_idx₀_eq : (p_j.vertices.get ⟨idx₀, hidx₀_lt⟩).1 = target := by
                have h1 : (p_j.vertices.get ⟨idx₀ - 1 + 1, hstep_idx⟩).1 =
                          (p_j.vertices.get ⟨idx₀, hidx₀_lt⟩).1 := by
                  simp only [Nat.sub_add_cancel hidx₀_pos]
                have h2 : (p_j.vertices.get ⟨idx₀ - 1, Nat.lt_of_succ_lt hstep_idx⟩).1 =
                          (p_j.vertices.get ⟨idx₀ - 1, hidx₀_pred_lt⟩).1 := rfl
                rcases hstep with hstep0 | hstep1
                · -- x(idx₀) = x(idx₀ - 1), but x(idx₀ - 1) < target ≤ x(idx₀), contradiction
                  rw [h1, h2] at hstep0
                  omega
                · -- x(idx₀) = x(idx₀ - 1) + 1
                  rw [h1, h2] at hstep1
                  omega
              exact ⟨idx₀, hidx₀_lt, hx_idx₀_eq⟩
            obtain ⟨idx, hidx, hx_eq⟩ := h_exists
            -- Now show y > 1 at this index
            -- If y = 1, then vertex is (μ_i - i, 1), which is not in path j
            refine ⟨idx, hidx, hx_eq, ?_⟩
            by_contra hy_le
            push Not at hy_le
            -- y ≤ 1, but y ≥ 1 (since path starts at y = 1 and y increases)
            have hy_ge : (p_j.vertices.get ⟨idx, hidx⟩).2 ≥ 1 := by
              have hbd := LGV.integerLattice_path_vertices_bounded p_j idx hidx
              rw [hstart_j] at hbd
              exact hbd.2.2.1
            have hy_eq : (p_j.vertices.get ⟨idx, hidx⟩).2 = 1 := by omega
            -- So vertex is (μ_i - i, 1)
            have hv_eq : p_j.vertices.get ⟨idx, hidx⟩ = ((mu i : ℤ) - (i.val : ℤ), 1) := by
              ext <;> [exact hx_eq; exact hy_eq]
            -- But (μ_i - i, 1) is not in path j
            have hmem : p_j.vertices.get ⟨idx, hidx⟩ ∈ p_j.vertices := List.get_mem p_j.vertices ⟨idx, hidx⟩
            rw [hv_eq] at hmem
            exact h_not_in_j hmem

          obtain ⟨idx_j_x₀, hidx_j_x₀, hx_j_x₀, hy_j_x₀⟩ := hj_visits_x₀
          -- Key insight for the base case (j = i + 1):
          -- At x = x₀ = μ_i - i, path i starts at y = 1, while path j is at y > 1.
          -- Since paths don't intersect, this "path j above path i" property is maintained.
          --
          -- Define x₀ (path i's starting x-coordinate) and x₁ (where we compare heights)
          let x₀ : ℤ := (mu i : ℤ) - (i.val : ℤ)
          let x₁ : ℤ := (mu i : ℤ) - (i.val : ℤ) + k
          
          -- Path i has a vertex at x₀ (its start)
          have hx₀_p_i : ∃ (idx : ℕ) (hidx : idx < p_i.vertices.length),
              (p_i.vertices.get ⟨idx, hidx⟩).1 = x₀ := by
            have hlen_pos : 0 < p_i.vertices.length := List.length_pos_of_ne_nil p_i.nonempty
            refine ⟨0, hlen_pos, ?_⟩
            have hstart_eq : p_i.vertices.get ⟨0, hlen_pos⟩ = p_i.start := by
              simp only [LGV.SimpleDigraph.Path.start, List.head_eq_getElem, List.get_eq_getElem]
            rw [hstart_eq, hstart_i]
          
          -- Path j has a vertex at x₀ (from hj_visits_x₀)
          have hx₀_p_j : ∃ (idx : ℕ) (hidx : idx < p_j.vertices.length),
              (p_j.vertices.get ⟨idx, hidx⟩).1 = x₀ := ⟨idx_j_x₀, hidx_j_x₀, hx_j_x₀⟩
          
          -- Non-intersection: path i and j share no vertices
          have hni_ij : ∀ v, v ∈ p_i.vertices → v ∉ p_j.vertices := by
            intro v hv_in_i hv_in_j
            apply hni i j hij_ne
            exact ⟨v, hv_in_i, hv_in_j⟩
          
          -- At x₀, path j's y > path i's y for ALL pairs of vertices at x₀
          -- This is the key lemma: path i at x₀ has only vertices with y ∈ {1, 2, ..., m}
          -- where m is the max y of path i at x₀. Path j at x₀ has y > 1 and disjoint
          -- from path i's y-values, so path j's y > m ≥ path i's y.
          have h_above_at_x₀ : ∀ (idx_p : ℕ) (hidx_p : idx_p < p_i.vertices.length)
              (idx_p' : ℕ) (hidx_p' : idx_p' < p_j.vertices.length),
              (p_i.vertices.get ⟨idx_p, hidx_p⟩).1 = x₀ →
              (p_j.vertices.get ⟨idx_p', hidx_p'⟩).1 = x₀ →
              (p_j.vertices.get ⟨idx_p', hidx_p'⟩).2 > (p_i.vertices.get ⟨idx_p, hidx_p⟩).2 := by
            intro idx_p hidx_p idx_p' hidx_p' hx_p hx_p'
            -- Path i at x₀ has y ≥ 1 (starts at y = 1)
            -- Path i's vertices at x₀ are consecutive y-values starting from 1
            -- Path j at x₀ has y > 1 (from hj_visits_x₀) and disjoint from path i
            -- 
            -- Key insight: at x₀ = start.x of path i, path i's vertices at x₀
            -- form a consecutive sequence {(x₀, 1), (x₀, 2), ..., (x₀, m)}.
            -- Path j's vertices at x₀ are disjoint (non-intersection) and have y > 1.
            -- So path j's y-values at x₀ are in ℕ≥2 \ {2, ..., m} = {m+1, m+2, ...}.
            -- Therefore path j's y > m ≥ path i's y at x₀.
            --
            -- The proof uses that path i at x₀ starts at y = 1 (index 0).
            have hlen_pos_i : 0 < p_i.vertices.length := List.length_pos_of_ne_nil p_i.nonempty
            have hstart_at_x₀ : (p_i.vertices.get ⟨0, hlen_pos_i⟩).1 = x₀ := by
              have hstart_eq : p_i.vertices.get ⟨0, hlen_pos_i⟩ = p_i.start := by
                simp only [LGV.SimpleDigraph.Path.start, List.head_eq_getElem, List.get_eq_getElem]
              rw [hstart_eq, hstart_i]
            have hstart_y : (p_i.vertices.get ⟨0, hlen_pos_i⟩).2 = 1 := by
              have hstart_eq : p_i.vertices.get ⟨0, hlen_pos_i⟩ = p_i.start := by
                simp only [LGV.SimpleDigraph.Path.start, List.head_eq_getElem, List.get_eq_getElem]
              rw [hstart_eq, hstart_i]
            -- Path i's vertex at idx_p has x = x₀ and y ≥ 1
            have hy_p_ge : (p_i.vertices.get ⟨idx_p, hidx_p⟩).2 ≥ 1 := by
              have hbd := LGV.integerLattice_path_vertices_bounded p_i idx_p hidx_p
              rw [hstart_i] at hbd
              exact hbd.2.2.1
            -- The y-coordinate at idx_p is between 1 and some max value
            -- Use integerLattice_path_y_contiguous_at_x to show path i covers all y in [1, y_p]
            -- Since path j's vertex at idx_p' has the same x = x₀ and y > 1,
            -- and paths don't intersect, path j's y must be > path i's max y at x₀.
            --
            -- Simpler argument: path i at x₀ has consecutive y-values from 1.
            -- If path j at x₀ has y = y_j, and y_j ≤ y_p, then (x₀, y_j) is in path i
            -- (by contiguity), contradicting non-intersection.
            by_contra h_not_above
            push Not at h_not_above
            -- So y_j ≤ y_p
            let y_p := (p_i.vertices.get ⟨idx_p, hidx_p⟩).2
            let y_j := (p_j.vertices.get ⟨idx_p', hidx_p'⟩).2
            -- y_j ≥ 1 (from hy_j_x₀ we know y > 1 for the specific idx_j_x₀, but we need it for idx_p')
            have hy_j_ge : y_j ≥ 1 := by
              have hbd := LGV.integerLattice_path_vertices_bounded p_j idx_p' hidx_p'
              rw [hstart_j] at hbd
              exact hbd.2.2.1
            -- Use integerLattice_path_y_contiguous_at_x: path i covers all y in [1, y_p] at x₀
            -- Since y_j ∈ [1, y_p] (by hy_j_ge and h_not_above), (x₀, y_j) ∈ path i
            have h_contiguous := integerLattice_path_y_contiguous_at_x p_i x₀
              0 idx_p hlen_pos_i hidx_p (Nat.zero_le _) hstart_at_x₀ hx_p y_j
              (by simp only [y_j]; rw [hstart_y]; exact hy_j_ge) h_not_above
            obtain ⟨k_i, hk_i, _, _, hx_k_i, hy_k_i⟩ := h_contiguous
            -- So path i has vertex (x₀, y_j) at index k_i
            have hv_i : p_i.vertices.get ⟨k_i, hk_i⟩ = (x₀, y_j) := by
              ext <;> [exact hx_k_i; exact hy_k_i]
            -- Path j has vertex (x₀, y_j) at index idx_p'
            have hv_j : p_j.vertices.get ⟨idx_p', hidx_p'⟩ = (x₀, y_j) := by
              ext <;> [exact hx_p'; rfl]
            -- But (x₀, y_j) is in both paths, contradicting non-intersection
            have hmem_i : (x₀, y_j) ∈ p_i.vertices := by
              rw [← hv_i]; exact List.get_mem p_i.vertices ⟨k_i, hk_i⟩
            have hmem_j : (x₀, y_j) ∈ p_j.vertices := by
              rw [← hv_j]; exact List.get_mem p_j.vertices ⟨idx_p', hidx_p'⟩
            exact hni_ij (x₀, y_j) hmem_i hmem_j
          
          -- Now use paths_above_at_x_stays_above to extend to x₁
          -- First, establish that both paths visit x₁
          -- Path i visits x₁ at its k-th east step
          have hx₁_ge_x₀ : x₁ ≥ x₀ := by simp only [x₁, x₀]; omega
          
          -- Get the y-coordinates at x₁ from lgvPathEastStepYCoords_at_x
          -- For path i: the k-th east step is at x = start_x + k = μ_i - i + k = x₁
          have hk_lt_ycoords_i : k < (lgvPathEastStepYCoords p_i.vertices).length := by
            have hlen_eq : (lgvPathEastStepYCoords p_i.vertices).length = 
                ((pathTupleToLatticePaths lam mu pt) i).eastStepHeights.length := by
              simp only [pathTupleToLatticePaths, lgvPathToLatticePath, p_i]
              simp only [lgvYCoordsToFinN, List.length_pmap]
            rw [hlen_eq]; exact hk
          have h_i_at_x₁ := lgvPathEastStepYCoords_at_x p_i k hk_lt_ycoords_i
          obtain ⟨idx_i_x₁, hidx_i_x₁, hx_i_x₁, hy_i_x₁⟩ := h_i_at_x₁
          -- Verify x-coordinate matches x₁
          have hx_i_x₁_eq : (p_i.vertices.get ⟨idx_i_x₁, hidx_i_x₁⟩).1 = x₁ := by
            rw [hx_i_x₁]
            -- p_i.start.1 = (mu i : ℤ) - (i.val : ℤ) from hstart_i
            have hstart_x : p_i.start.1 = (mu i : ℤ) - (i.val : ℤ) := by
              simp only [p_i, hstart_i]
            rw [hstart_x]
          
          -- For path j: the k'-th east step is at x = start_x + k' = μ_j - j + k'
          -- We need to show this equals x₁ = μ_i - i + k
          -- From hcol: mu i + k = mu j + k', so μ_i - i + k = μ_j - j + k' + (j - i)
          -- Since j = i + 1, we get μ_i - i + k = μ_j - j + k' + 1
          -- So path j's k'-th east step is at x = x₁ - 1, and AFTER the east step, path j is at x₁
          have hk'_lt_ycoords_j : k' < (lgvPathEastStepYCoords p_j.vertices).length := by
            have hlen_eq : (lgvPathEastStepYCoords p_j.vertices).length = 
                ((pathTupleToLatticePaths lam mu pt) j).eastStepHeights.length := by
              simp only [pathTupleToLatticePaths, lgvPathToLatticePath, p_j]
              simp only [lgvYCoordsToFinN, List.length_pmap]
            rw [hlen_eq]; exact hk'
          have h_j_at_kprime := lgvPathEastStepYCoords_at_x p_j k' hk'_lt_ycoords_j
          obtain ⟨idx_j_kprime, hidx_j_kprime, hx_j_kprime, hy_j_kprime⟩ := h_j_at_kprime
          -- Path j's k'-th east step starts at x = μ_j - j + k'
          have hx_j_kprime_val : (p_j.vertices.get ⟨idx_j_kprime, hidx_j_kprime⟩).1 = 
              (mu j : ℤ) - (j.val : ℤ) + k' := by
            rw [hx_j_kprime]
            have hstart_x : p_j.start.1 = (mu j : ℤ) - (j.val : ℤ) := by
              simp only [p_j, hstart_j]
            rw [hstart_x]
          -- The x-coordinate where path j's k'-th east step starts
          -- From hcol: mu i + k = mu j + k'
          -- So μ_j - j + k' = μ_j + k' - j = (μ_i + k) - j = μ_i + k - (i + 1) = μ_i - i + k - 1 = x₁ - 1
          have hx_j_eq_x₁_minus_1 : (mu j : ℤ) - (j.val : ℤ) + k' = x₁ - 1 := by
            simp only [x₁]
            have h1 : (mu i : ℕ) + k = (mu j : ℕ) + k' := hcol
            have h2 : j.val = i.val + 1 := hj_eq
            omega
          -- After the east step, path j is at x = x₁
          -- The east step increases x by 1, so the next vertex is at x = x₁
          -- Use lgvPathEastStepYCoords_at_x_is_east_step to get the next vertex
          have hidx_j_next : idx_j_kprime + 1 < p_j.vertices.length := by
            -- The k'-th east step is not the last step (path ends at y = N, not at this east step)
            -- Actually, we need to show idx_j_kprime + 1 < length
            -- This follows from the fact that there are more vertices after the east step
            -- The path ends at (λ_j - j, N), and the k'-th east step is at x = x₁ - 1 < λ_j - j
            -- So there are more vertices after this east step
            have hfinish_x : p_j.finish.1 = (lam j : ℤ) - (j.val : ℤ) := by
              rw [hfinish_j]
            have hx_lt_finish : (p_j.vertices.get ⟨idx_j_kprime, hidx_j_kprime⟩).1 < p_j.finish.1 := by
              rw [hx_j_kprime_val, hfinish_x, hx_j_eq_x₁_minus_1]
              simp only [x₁]
              -- Need: μ_i - i + k - 1 < λ_j - j
              -- From h_col_bound: mu i + k < lam j
              -- So μ_i + k < λ_j, hence μ_i - i + k < λ_j - i = λ_j - j + (j - i) = λ_j - j + 1
              -- So μ_i - i + k - 1 < λ_j - j
              omega
            -- If idx_j_kprime is the last index, then the vertex is the finish
            by_contra h_last
            push Not at h_last
            -- h_last : p_j.vertices.length ≤ idx_j_kprime + 1
            -- We know idx_j_kprime < p_j.vertices.length (from hidx_j_kprime)
            -- So idx_j_kprime + 1 ≤ p_j.vertices.length
            -- Combined with h_last, we get idx_j_kprime + 1 = p_j.vertices.length
            have hidx_eq_last : idx_j_kprime = p_j.vertices.length - 1 := by
              have h1 : idx_j_kprime + 1 ≤ p_j.vertices.length := hidx_j_kprime
              have h2 : p_j.vertices.length ≤ idx_j_kprime + 1 := h_last
              omega
            have hfinish_eq : p_j.vertices.get ⟨idx_j_kprime, hidx_j_kprime⟩ = p_j.finish := by
              simp only [LGV.SimpleDigraph.Path.finish, List.getLast_eq_getElem, List.get_eq_getElem]
              congr 1
            rw [hfinish_eq] at hx_lt_finish
            exact (lt_irrefl _ hx_lt_finish)
          have h_east_step := lgvPathEastStepYCoords_at_x_is_east_step p_j k' hk'_lt_ycoords_j
            idx_j_kprime hidx_j_kprime hx_j_kprime hy_j_kprime hidx_j_next
          -- The next vertex is at x = x₁ with the same y-coordinate
          have hx_j_next : (p_j.vertices.get ⟨idx_j_kprime + 1, hidx_j_next⟩).1 = x₁ := by
            rw [h_east_step.1, hx_j_kprime_val, hx_j_eq_x₁_minus_1]
            ring
          have hy_j_next : (p_j.vertices.get ⟨idx_j_kprime + 1, hidx_j_next⟩).2 = 
              (lgvPathEastStepYCoords p_j.vertices)[k'] := by
            rw [h_east_step.2, hy_j_kprime]
          
          -- Now apply paths_above_at_x_stays_above
          have hx₁_p_i : ∃ (idx : ℕ) (hidx : idx < p_i.vertices.length),
              (p_i.vertices.get ⟨idx, hidx⟩).1 = x₁ := ⟨idx_i_x₁, hidx_i_x₁, hx_i_x₁_eq⟩
          have hx₁_p_j : ∃ (idx : ℕ) (hidx : idx < p_j.vertices.length),
              (p_j.vertices.get ⟨idx, hidx⟩).1 = x₁ := ⟨idx_j_kprime + 1, hidx_j_next, hx_j_next⟩
          
          have h_above_at_x₁ := paths_above_at_x_stays_above p_i p_j hni_ij x₀ hx₀_p_i hx₀_p_j
            h_above_at_x₀ x₁ hx₁_ge_x₀ hx₁_p_i hx₁_p_j
          
          -- Apply to our specific indices
          have h_y_comparison := h_above_at_x₁ idx_i_x₁ hidx_i_x₁ (idx_j_kprime + 1) hidx_j_next
            hx_i_x₁_eq hx_j_next
          -- h_y_comparison : y_j > y_i at x₁
          -- y_i = lgvPathEastStepYCoords p_i.vertices [k] = eastStepHeights[k].val + 1
          -- y_j = lgvPathEastStepYCoords p_j.vertices [k'] = eastStepHeights[k'].val + 1
          
          -- Convert to eastStepHeights comparison
          -- eastStepHeights[k] = lgvYCoordsToFinN (lgvPathEastStepYCoords ...) [k]
          -- lgvYCoordsToFinN maps y to (y - 1).toNat as Fin N
          -- So eastStepHeights[k].val = (lgvPathEastStepYCoords ...)[k] - 1
          simp only [pathTupleToLatticePaths, lgvPathToLatticePath] at hk hk' ⊢
          -- Need to show: eastStepHeights[k'] > eastStepHeights[k]
          -- i.e., (lgvYCoordsToFinN ...)[k'].val > (lgvYCoordsToFinN ...)[k].val
          -- i.e., (lgvPathEastStepYCoords p_j.vertices)[k'] - 1 > (lgvPathEastStepYCoords p_i.vertices)[k] - 1
          -- i.e., (lgvPathEastStepYCoords p_j.vertices)[k'] > (lgvPathEastStepYCoords p_i.vertices)[k]
          -- This follows from h_y_comparison since y_i = ycoords[k] and y_j = ycoords[k']
          rw [hy_i_x₁] at h_y_comparison
          rw [hy_j_next] at h_y_comparison
          -- h_y_comparison : (lgvPathEastStepYCoords p_j.vertices)[k'] > (lgvPathEastStepYCoords p_i.vertices)[k]
          -- Convert to Fin comparison
          have hfinish_i := pt.finishes i
          unfold jacobiTrudiTargetVertex jacobiTrudiTargetX at hfinish_i
          have hbnd_i : ∀ y ∈ lgvPathEastStepYCoords p_i.vertices, 1 ≤ y ∧ y ≤ N := by
            intro y hy
            have hbnd := lgvPathEastStepYCoords_bounded p_i.vertices p_i.nonempty p_i.arcs_valid y hy
            simp only [LGV.SimpleDigraph.Path.start, LGV.SimpleDigraph.Path.finish] at hstart_i hfinish_i
            rw [hstart_i, hfinish_i] at hbnd
            simp at hbnd
            exact hbnd
          have hbnd_j : ∀ y ∈ lgvPathEastStepYCoords p_j.vertices, 1 ≤ y ∧ y ≤ N := by
            intro y hy
            have hbnd := lgvPathEastStepYCoords_bounded p_j.vertices p_j.nonempty p_j.arcs_valid y hy
            simp only [LGV.SimpleDigraph.Path.start, LGV.SimpleDigraph.Path.finish] at hstart_j hfinish_j
            rw [hstart_j, hfinish_j] at hbnd
            simp at hbnd
            exact hbnd
          have hk_mem : (lgvPathEastStepYCoords p_i.vertices)[k] ∈ lgvPathEastStepYCoords p_i.vertices :=
            List.getElem_mem hk_lt_ycoords_i
          have hk'_mem : (lgvPathEastStepYCoords p_j.vertices)[k'] ∈ lgvPathEastStepYCoords p_j.vertices :=
            List.getElem_mem hk'_lt_ycoords_j
          have hbnd_k := hbnd_i _ hk_mem
          have hbnd_k' := hbnd_j _ hk'_mem
          -- The Fin values are (y - 1).toNat
          simp only [lgvYCoordsToFinN, List.getElem_pmap]
          -- Goal: Fin.mk ((ycoords_j[k'] - 1).toNat) _ > Fin.mk ((ycoords_i[k] - 1).toNat) _
          simp only [Fin.lt_def]
          -- Goal: (ycoords_j[k'] - 1).toNat > (ycoords_i[k] - 1).toNat
          have h1 : ((lgvPathEastStepYCoords p_i.vertices)[k] - 1).toNat = 
              (lgvPathEastStepYCoords p_i.vertices)[k].toNat - 1 := by
            have hge : (lgvPathEastStepYCoords p_i.vertices)[k] ≥ 1 := hbnd_k.1
            omega
          have h2 : ((lgvPathEastStepYCoords p_j.vertices)[k'] - 1).toNat = 
              (lgvPathEastStepYCoords p_j.vertices)[k'].toNat - 1 := by
            have hge : (lgvPathEastStepYCoords p_j.vertices)[k'] ≥ 1 := hbnd_k'.1
            omega
          rw [h1, h2]
          omega

        -- Now derive contradiction
        exact absurd h_heights (not_lt.mpr h_not_lt)
    · -- Inductive case: j > i + 1
      -- Use the intermediate row l = i + 1
      have h_j_gt : j.val > i.val + 1 := by omega
      have hl_lt_N : i.val + 1 < N := by
        have := j.is_lt
        omega
      let l : Fin N := ⟨i.val + 1, hl_lt_N⟩
      -- k_l = μ_i + k - μ_l is the index for row l at the same tableau column
      have hmu_l : mu l ≤ mu i := hmu i l (Fin.le_of_lt (by simp only [l, Fin.lt_def]; omega : i < l))
      have hlam_l : lam j ≤ lam l := hlam l j (by simp only [l, Fin.le_iff_val_le_val]; omega)
      let k_l : ℕ := mu i + k - mu l
      have hk_l_eq : mu l + k_l = mu i + k := by
        show mu l + (mu i + k - mu l) = mu i + k
        omega
      -- Verify k_l is a valid index
      have hk_l_lt : k_l < ((pathTupleToLatticePaths lam mu pt) l).eastStepHeights.length := by
        -- k_l = mu i + k - mu l < lam l - mu l
        -- This follows from mu i + k = mu j + k' < lam j ≤ lam l
        -- First establish that length = lam l - mu l
        have hlen_l : ((pathTupleToLatticePaths lam mu pt) l).eastStepHeights.length = lam l - mu l := by
          have h := ((pathTupleToLatticePaths lam mu pt) l).length_eq
          -- h : length = ((lam l : ℤ) - l.val - ((mu l : ℤ) - l.val)).toNat
          have hcont_l : mu l ≤ lam l := hcontained l
          simp only [sub_sub_sub_cancel_right] at h
          omega
        rw [hlen_l]
        -- Now goal is k_l < lam l - mu l
        -- From hk' : k' < length_j = lam j - mu j
        have hlen_j : ((pathTupleToLatticePaths lam mu pt) j).eastStepHeights.length = lam j - mu j := by
          have h := ((pathTupleToLatticePaths lam mu pt) j).length_eq
          have hcont_j : mu j ≤ lam j := hcontained j
          simp only [sub_sub_sub_cancel_right] at h
          omega
        have hk'_bound : k' < lam j - mu j := by rw [← hlen_j]; exact hk'
        have h1 : mu j + k' < lam j := by omega
        have h2 : mu i + k < lam j := by omega
        have h3 : mu i + k ≤ lam l := Nat.le_of_lt (Nat.lt_of_lt_of_le h2 hlam_l)
        show k_l < lam l - mu l
        simp only [k_l]
        omega
      -- Apply IH for (i, l) with d' = 0 < d
      have h_i_lt_l : i < l := by
        simp only [l, Fin.lt_def]
        omega
      have h_d1_pos : 0 < l.val - i.val := by simp [l]
      have h_d1_eq : l.val - i.val = 0 + 1 := by simp [l]
      have h1 : ((pathTupleToLatticePaths lam mu pt) i).eastStepHeights[k] <
          ((pathTupleToLatticePaths lam mu pt) l).eastStepHeights[k_l] := by
        have h_d1_lt : 0 < d := by omega
        exact ih 0 h_d1_lt i l h_i_lt_l k hk k_l hk_l_lt hk_l_eq.symm h_d1_pos h_d1_eq
      -- Apply IH for (l, j) with d' = j - l - 1 < d
      have h_l_lt_j : l < j := by simp [l]; exact h_j_gt
      have h_d2_pos : 0 < j.val - l.val := Nat.sub_pos_of_lt h_l_lt_j
      have h_d2_eq : j.val - l.val = (d - 1) + 1 := by simp [l]; omega
      have h_d2_lt : d - 1 < d := Nat.sub_lt (by omega : 0 < d) Nat.one_pos
      have hcol_l : mu l + k_l = mu j + k' := by rw [hk_l_eq, hcol]
      have h2 : ((pathTupleToLatticePaths lam mu pt) l).eastStepHeights[k_l] <
          ((pathTupleToLatticePaths lam mu pt) j).eastStepHeights[k'] := by
        exact ih (d - 1) h_d2_lt l j h_l_lt_j k_l hk_l_lt k' hk' hcol_l h_d2_pos h_d2_eq
      -- Combine by transitivity
      exact Fin.lt_trans h1 h2

/-- Convert a non-intersecting PathTuple to a Nipat. -/
noncomputable def pathTupleToNipat (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i)
    (pt : LGV.PathTuple LGV.integerLattice N
      (jacobiTrudiSourceVertex mu) (jacobiTrudiTargetVertex lam))
    (hni : pt.isNonIntersecting) :
    Nipat lam mu hlam hmu hcontained where
  paths := pathTupleToLatticePaths lam mu pt
  colStrictPaths := isNonIntersecting_implies_colStrictPaths lam mu hlam hmu hcontained pt hni
/-!
## Special Cases

When μ = 0 (the empty partition), we get formulas for non-skew Schur polynomials.
-/
/-!
## Symmetry of Skew Schur Polynomials via Jacobi-Trudi

The Jacobi-Trudi formula provides an alternative proof that skew Schur polynomials
are symmetric, without relying on the Bender-Knuth involution.

**Key insight**: The Jacobi-Trudi matrix has entries h_{λᵢ - μⱼ - i + j}, where h_n
is the n-th complete homogeneous symmetric polynomial. Since each h_n is symmetric
and the determinant is a polynomial in the entries, the determinant is also symmetric.

This provides a **sorry-free** proof of symmetry for skew Schur polynomials,
complementing the Bender-Knuth approach in SchurBasics.lean (which is also sorry-free).
-/

end SymmetricFunctions

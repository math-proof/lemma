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
import Instance.Combinatorics.Young.PieriJacobiTrudi.Part13
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

end SymmetricFunctions

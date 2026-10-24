/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
/-!
# N-Partitions

This file provides the canonical definition of `NPartition N`, which represents
a weakly decreasing N-tuple of nonnegative integers (Definition def.sf.Npar in the source).

## Main definitions

* `IsNPartition` - predicate for N-tuples that are weakly decreasing
* `NPartition N` - a weakly decreasing N-tuple of nonnegative integers
* `NPartition.parts` - the entries of the partition as a function `Fin N → ℕ`
* `NPartition.antitone` - proof that the entries are weakly decreasing
* `NPartition.size` - the sum of all entries
* `NPartition.zero` - the zero partition (0, 0, ..., 0)
* `NPartition.add` - component-wise addition of N-partitions
* `NPartition.youngDiagram` - the Young diagram Y(λ) as a `Finset (Fin N × ℕ)`
* `NPartition.skewYoungDiagram` - the skew Young diagram Y(λ/μ) as a `Finset (Fin N × ℕ)`
* `NPartition.instFintypeBounded` - `Fintype` instance for partitions with bounded entries
* `NPartition.instFintypeSizeBounded` - `Fintype` instance for partitions with bounded size

## Design notes

This file provides the canonical `NPartition` structure. We use `antitone` as the
field name since it matches Mathlib conventions.

The weakly decreasing condition means: if `i ≤ j` then `parts j ≤ parts i`.
This is equivalent to `Antitone parts` in Mathlib terminology.

## Duplicate definitions

For historical reasons, there is a local `NPartition` definition in:

1. `PieriJacobiTrudi.lean` (`SymmetricFunctions.NPartition`):
   Uses `weaklyDecreasing` field name.

Both definitions are semantically equivalent (representing weakly decreasing
N-tuples of natural numbers). The local definition is retained to avoid large
refactoring of the extensive APIs built on top of it. Future work may consolidate
these definitions.

**Note**: `MonomialSymmetric.lean` and `SchurBasics.lean` have been migrated to use
the canonical definition via `abbrev` or direct import.

## Compatibility

For backwards compatibility with code using other field names:
- `NPartition.monotone` is an alias for `NPartition.antitone`
- `NPartition.weaklyDecreasing` is an alias for `NPartition.antitone`

## Migration Guide

The `NPartition` structure is defined in this file (canonical) and has one remaining
local definition:

| File                     | Namespace                       | Field name        | Status           |
|--------------------------|--------------------------------|-------------------|------------------|
| `NPartition.lean` (this) | (top-level)                    | `antitone`        | **Canonical**    |
| `PieriJacobiTrudi.lean`  | `SymmetricFunctions`           | `weaklyDecreasing`| Local (with bridge) |
| `MonomialSymmetric.lean` | `AlgebraicCombinatorics.SymmetricFunctions`   | (abbrev)          | ✓ Migrated       |
| `SchurBasics.lean`       | (top-level)                    | (import)          | ✓ Migrated       |

To migrate a file to use this shared definition:

1. Add `import AlgebraicCombinatorics.SymmetricFunctions.NPartition` to imports
2. Remove the local `structure NPartition` definition
3. If in a namespace, use `open NPartition` or create a local alias
4. Replace field accesses:
   - `.monotone` → `.antitone` or use the `monotone` alias theorem
   - `.weaklyDecreasing` → `.antitone` or use the `weaklyDecreasing` alias theorem
5. For constructors, use `NPartition.mk` with `antitone` field, or use `NPartition.mk'`
   which accepts the explicit predicate form

## References

* Source: AlgebraicCombinatorics/tex/SymmetricFunctions/MonomialSymmetric.tex (Definition def.sf.Npar)
-/


open Finset BigOperators

variable {N : ℕ}
/-! ## IsNPartition predicate

This predicate characterizes N-tuples that are weakly decreasing. It is equivalent
to `Antitone` for functions `Fin N → ℕ`. -/


/-- An N-partition predicate: an N-tuple is an N-partition if it is weakly decreasing.
    This is equivalent to `Antitone` for functions `Fin N → ℕ`.
    (Used throughout the source) -/
def IsNPartition (lam : Fin N → ℕ) : Prop :=
  ∀ i j : Fin N, i ≤ j → lam j ≤ lam i

/-- `IsNPartition` is decidable since it's a finite conjunction of decidable inequalities. -/
instance IsNPartition.instDecidable (lam : Fin N → ℕ) : Decidable (IsNPartition lam) :=
  inferInstanceAs (Decidable (∀ i j : Fin N, i ≤ j → lam j ≤ lam i))

namespace NPartition

variable {N : ℕ}

end NPartition

/-- An N-partition is a weakly decreasing N-tuple of nonnegative integers.
    (Definition def.sf.Npar)

    This is represented as a function `Fin N → ℕ` that is antitone
    (i.e., `i ≤ j → parts j ≤ parts i`).

    The field is named `antitone` to match Mathlib conventions. -/
structure NPartition (N : ℕ) where
  /-- The entries of the N-partition as a function from `Fin N` to `ℕ` -/
  parts : Fin N → ℕ
  /-- The entries are weakly decreasing (antitone) -/
  antitone : Antitone parts

namespace NPartition

variable {N : ℕ}
/-! ## Compatibility aliases for field names -/
/-! ## Basic properties -/


/-- Two N-partitions are equal if and only if their parts are equal. -/
@[ext]
theorem ext {μ ν : NPartition N} (h : μ.parts = ν.parts) : μ = ν := by
  cases μ; cases ν; simp_all

/-- Extensionality in terms of parts equality. -/
theorem parts_ext_iff {μ ν : NPartition N} : μ = ν ↔ μ.parts = ν.parts :=
  ⟨fun h => h ▸ rfl, ext⟩

/-- Decidable equality for N-partitions. -/
instance instDecidableEq : DecidableEq (NPartition N) := fun μ ν =>
  decidable_of_iff (μ.parts = ν.parts) parts_ext_iff.symm
/-! ## The zero partition -/


/-- The zero N-partition (0, 0, ..., 0) -/
def zero : NPartition N where
  parts := fun _ => 0
  antitone := fun _ _ _ => le_refl 0

instance : Zero (NPartition N) := ⟨zero⟩

instance : Inhabited (NPartition N) := ⟨0⟩

@[simp]
theorem zero_parts_apply (i : Fin N) : (0 : NPartition N).parts i = 0 := rfl
/-! ## Size (weight) of a partition -/


/-- The size (or weight) of an N-partition is the sum of its entries.
    If μ = (μ₁, μ₂, ..., μ_N), then |μ| = μ₁ + μ₂ + ... + μ_N. -/
def size (μ : NPartition N) : ℕ := ∑ i, μ.parts i

/-- Each entry of an N-partition is bounded by the size. -/
theorem parts_le_size (μ : NPartition N) (i : Fin N) : μ.parts i ≤ μ.size := by
  simp only [size]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
/-! ## Addition of N-partitions

Component-wise addition of N-partitions. Since both partitions are antitone
(weakly decreasing), their component-wise sum is also antitone, so the result
is a valid N-partition without needing to sort.

This is the canonical `Add` instance for `NPartition`, used by all files including
`MonomialSymmetric.lean`.
-/


/-- Component-wise addition of N-partitions.
    Since both partitions are antitone (weakly decreasing), their sum is also antitone. -/
def add (μ ν : NPartition N) : NPartition N where
  parts i := μ.parts i + ν.parts i
  antitone := fun _ _ hij => Nat.add_le_add (μ.antitone hij) (ν.antitone hij)

instance : Add (NPartition N) := ⟨add⟩

/-- The parts of a sum of N-partitions equals the component-wise sum. -/
@[simp]
theorem add_parts (μ ν : NPartition N) (i : Fin N) : (μ + ν).parts i = μ.parts i + ν.parts i := rfl

/-- Addition of N-partitions is commutative. -/
theorem add_comm (μ ν : NPartition N) : μ + ν = ν + μ := by
  ext i
  simp [Nat.add_comm]

/-- Adding zero to an N-partition gives the same N-partition. -/
@[simp]
theorem add_zero (μ : NPartition N) : μ + 0 = μ := by
  ext i
  simp [add_parts]

/-- Adding an N-partition to zero gives the same N-partition. -/
@[simp]
theorem zero_add (μ : NPartition N) : 0 + μ = μ := by
  rw [add_comm, add_zero]

/-- Addition of N-partitions is associative. -/
theorem add_assoc (μ ν ρ : NPartition N) : μ + ν + ρ = μ + (ν + ρ) := by
  ext i
  simp [Nat.add_assoc]

/-- `NPartition N` forms an `AddCommMonoid` under component-wise addition.
    This enables using generic Mathlib lemmas about `AddCommMonoid` with `NPartition`. -/
instance : AddCommMonoid (NPartition N) where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  nsmul := nsmulRec
/-! ## Coercion to function -/


/-- Coercion to a function. -/
instance : CoeFun (NPartition N) (fun _ => Fin N → ℕ) := ⟨parts⟩
/-! ## Partial order (containment) -/


/-- Containment of partitions: μ ≤ ν means μᵢ ≤ νᵢ for all i -/
instance instLE : LE (NPartition N) where
  le μ ν := ∀ i, μ.parts i ≤ ν.parts i

instance instPreorder : Preorder (NPartition N) where
  le := (· ≤ ·)
  le_refl := fun μ i => le_refl (μ.parts i)
  le_trans := fun μ ν ρ hab hbc i => le_trans (hab i) (hbc i)

instance instPartialOrder : PartialOrder (NPartition N) where
  le_antisymm := fun _ _ hab hba => ext (funext fun i => le_antisymm (hab i) (hba i))
/-! ## Fintype instances for bounded partitions -/


/-- The set of N-partitions with entries bounded by M is finite.
    This is useful for cardinality arguments in symmetric function theory. -/
noncomputable instance instFintypeBounded (M : ℕ) :
    Fintype { μ : NPartition N // ∀ i, μ.parts i ≤ M } := by
  -- Strategy: embed into Fin N → Fin (M + 1) which is finite
  let S := { f : Fin N → Fin (M + 1) // Antitone f }
  have hS : Fintype S := Subtype.fintype _
  let φ : { μ : NPartition N // ∀ i, μ.parts i ≤ M } → S := fun ⟨μ, hμ⟩ =>
    ⟨fun i => ⟨μ.parts i, Nat.lt_succ_of_le (hμ i)⟩, fun i j hij =>
      Fin.mk_le_mk.mpr (μ.antitone hij)⟩
  have hφ : Function.Injective φ := by
    intro ⟨μ₁, h₁⟩ ⟨μ₂, h₂⟩ heq
    apply Subtype.ext
    apply ext
    funext i
    exact Fin.val_eq_of_eq (congr_fun (congr_arg Subtype.val heq) i)
  exact Fintype.ofInjective φ hφ

/-- The set of N-partitions with size bounded by n is finite.
    This follows from the fact that if size ≤ n, then all entries are ≤ n.
    This is needed for counting SSYT of bounded content. -/
noncomputable instance instFintypeSizeBounded (n : ℕ) :
    Fintype { μ : NPartition N // μ.size ≤ n } := by
  -- If size ≤ n, then all entries are ≤ n (since each entry ≤ size)
  -- So we can embed into the bounded-entry type
  let T := { μ : NPartition N // ∀ i, μ.parts i ≤ n }
  have hT : Fintype T := instFintypeBounded n
  let φ : { μ : NPartition N // μ.size ≤ n } → T := fun ⟨μ, hμ⟩ =>
    ⟨μ, fun i => le_trans (parts_le_size μ i) hμ⟩
  have hφ : Function.Injective φ := by
    intro ⟨μ₁, _⟩ ⟨μ₂, _⟩ heq
    apply Subtype.ext
    exact Subtype.mk.inj (by simpa [φ] using heq)
  exact Fintype.ofInjective φ hφ

/-- The set of N-partitions with exact size n is finite.
    This is a subtype of the bounded-size type. -/
noncomputable instance instFintypeSizeEq (n : ℕ) :
    Fintype { μ : NPartition N // μ.size = n } := by
  have hBounded : Fintype { μ : NPartition N // μ.size ≤ n } := instFintypeSizeBounded n
  let φ : { μ : NPartition N // μ.size = n } → { μ : NPartition N // μ.size ≤ n } :=
    fun ⟨μ, hμ⟩ => ⟨μ, le_of_eq hμ⟩
  have hφ : Function.Injective φ := by
    intro ⟨μ₁, _⟩ ⟨μ₂, _⟩ heq
    apply Subtype.ext
    simpa [φ] using heq
  exact Fintype.ofInjective φ hφ

/-- The finite set of N-partitions with exact size n. -/
noncomputable def partitionsOfSize (n : ℕ) : Finset (NPartition N) :=
  (Finset.univ : Finset { μ : NPartition N // μ.size = n }).map
    ⟨Subtype.val, Subtype.val_injective⟩

/-- Decidable instance for partition containment. -/
instance instDecidableLE : DecidableRel (fun (μ ν : NPartition N) => μ ≤ ν) :=
  fun _ _ => Fintype.decidableForallFintype

/-- The zero N-partition is the minimum element -/
theorem zero_le (μ : NPartition N) : (0 : NPartition N) ≤ μ := fun i => by
  simp only [zero_parts_apply]
  exact Nat.zero_le _
/-! ## Length of a partition -/


/-- The length of an N-partition is the number of nonzero entries. -/
def length (μ : NPartition N) : ℕ := (Finset.univ.filter (fun i : Fin N => μ.parts i ≠ 0)).card
/-! ## Constructor with explicit predicate -/


/-- Construct an NPartition from a function and a proof that it satisfies the
    weakly decreasing predicate (in the explicit form used in SchurBasics.lean
    and PieriJacobiTrudi.lean). -/
def mk' (parts : Fin N → ℕ)
    (h : ∀ i j : Fin N, i ≤ j → parts j ≤ parts i) : NPartition N where
  parts := parts
  antitone := h
/-! ## Part accessor -/


/-- The i-th part of an N-partition (alias for `parts i`).
    This matches the naming in SchurBasics.lean. -/
def part (μ : NPartition N) (i : Fin N) : ℕ := μ.parts i
/-! ## Bijection with Nat.Partition (Proposition prop.sf.Npar-as-par)

There is a bijection between partitions of length ≤ N and N-partitions.
This is formalized in MonomialSymmetric.lean as `NPartition.equivPartition`.
Here we provide the basic conversion functions. -/


/-- Helper lemma: filtering out zeros doesn't change the sum. -/
theorem filter_ne_zero_sum (m : Multiset ℕ) : (m.filter (· ≠ 0)).sum = m.sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.filter_cons, Multiset.sum_cons]
    split_ifs with ha
    · simp [ih]
    · push_neg at ha; simp [ha, ih]

/-- Convert a partition (as a `Nat.Partition`) to an N-partition by padding with zeros.
    Requires that the partition has at most N parts.

    This corresponds to the map in Proposition prop.sf.Npar-as-par:
    (μ₁, μ₂, ..., μ_ℓ) ↦ (μ₁, μ₂, ..., μ_ℓ, 0, 0, ..., 0) -/
def ofPartition {n : ℕ} (p : Nat.Partition n) (_hp : Multiset.card p.parts ≤ N) : NPartition N where
  parts := fun i =>
    let sorted := p.parts.sort (· ≥ ·)
    if h : i.val < sorted.length then sorted.get ⟨i.val, h⟩ else 0
  antitone := by
    intro i j hij
    simp only
    split_ifs with hi hj hj
    · -- Both in range: use that sorted list is decreasing
      have hsorted : (p.parts.sort (· ≥ ·)).Pairwise (· ≥ ·) :=
        Multiset.pairwise_sort (r := (· ≥ ·)) p.parts
      exact List.Pairwise.rel_get_of_le hsorted hij
    · -- i in range, j out of range: contradiction since i ≤ j
      omega
    · -- i out of range: 0 ≤ anything
      exact Nat.zero_le _
    · -- both out of range
      exact le_refl 0

/-- Convert an N-partition to a partition by removing trailing zeros. -/
def toPartition (μ : NPartition N) : Nat.Partition μ.size where
  parts := (Finset.univ.val.map μ.parts).filter (· ≠ 0)
  parts_pos := by
    intro i hi
    simp only [Multiset.mem_filter, Multiset.mem_map, Finset.mem_val, Finset.mem_univ,
      true_and] at hi
    omega
  parts_sum := by
    simp only [size]
    have h : (Finset.univ.val.map μ.parts).sum = ∑ i, μ.parts i := by
      simp [Finset.sum_eq_multiset_sum]
    rw [← h]
    exact filter_ne_zero_sum _
/-! ## Young Diagram (Definition def.sf.ydiag)

The Young diagram Y(λ) of an N-partition λ is the set of cells (i, j) where
i ∈ [N] and j ∈ [λ_i].

Note: Mathlib has `YoungDiagram` which is more general (infinite diagrams).
Here we define a version specific to N-partitions. -/


/-- The Young diagram Y(λ) of an N-partition λ is the set of cells (i, j) where
    i ∈ Fin N and j < λ_i.
    Definition def.sf.ydiag in the source.

    Note: Mathlib has `YoungDiagram` which is more general (infinite diagrams).
    Here we define a version specific to N-partitions. -/
def youngDiagram (μ : NPartition N) : Finset (Fin N × ℕ) :=
  Finset.univ.biUnion fun i => (Finset.range (μ.parts i)).map
    ⟨fun j => (i, j), fun _ _ h => congr_arg Prod.snd h⟩

/-- Membership in a Young diagram: (i, j) ∈ Y(λ) iff j < λ_i.
    This is the 0-indexed version of the textbook condition j ∈ [λ_i].
    Definition def.sf.ydiag in the source. -/
theorem mem_youngDiagram {μ : NPartition N} {c : Fin N × ℕ} :
    c ∈ μ.youngDiagram ↔ c.2 < μ.parts c.1 := by
  simp only [youngDiagram, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨i, j, hj, rfl⟩
    exact hj
  · intro h
    exact ⟨c.1, c.2, h, rfl⟩

/-- Decidability of membership in Young diagram -/
instance youngDiagram_decidableMem (μ : NPartition N) :
    DecidablePred (· ∈ μ.youngDiagram) := fun c =>
  decidable_of_iff (c.2 < μ.parts c.1) mem_youngDiagram.symm
/-! ## Skew Young Diagram (Definition def.sf.skew-diag)

**This is the canonical `Finset` version of skew Young diagrams.**

The skew Young diagram Y(λ/μ) of two N-partitions λ and μ (where μ ⊆ λ componentwise)
is the set of cells in Y(λ) but not in Y(μ). In other words:
  Y(λ/μ) = {(i, j) | μ_i ≤ j < λ_i}

This uses 0-indexed columns (j starts from 0), following Mathlib/programming conventions.

**Alternative definitions:**
- `AlgebraicCombinatorics.skewYoungDiagram` in LittlewoodRichardson.lean returns a `Set`
  and uses 1-indexed columns: {(i, j) | μ_i < j ≤ λ_i}. This matches textbook conventions.
- `skewYoungDiagram` in SchurBasics.lean is a duplicate that requires `[NeZero N]`.
  Prefer this canonical version when possible.

The two indexing conventions are equivalent via the bijection (i, j) ↔ (i, j+1).
See `SchurBasics.skewYoungDiagram_equiv_LR` for the equivalence proof. -/


/-- The skew Young diagram Y(λ/μ) is the set difference Y(λ) \ Y(μ).
    This consists of cells (i, j) where μ_i ≤ j < λ_i.
    Definition def.sf.skew-diag in the source.

    **This is the canonical `Finset` version of skew Young diagrams.**
    
    Other versions exist for different use cases:
    - `AlgebraicCombinatorics.skewYoungDiagram` in LittlewoodRichardson.lean returns a `Set`
      and uses 1-indexed columns (textbook convention)
    - `skewYoungDiagram` in SchurBasics.lean is a duplicate that requires `[NeZero N]`
      (prefer this canonical version)

    **Indexing Convention**: Uses 0-indexed columns (Mathlib convention).
    - Here: (i, j) ∈ Y(λ/μ) iff μ_i ≤ j < λ_i
    - LittlewoodRichardson: (i, j) ∈ Y(λ/μ) iff μ_i < j ≤ λ_i (1-indexed)
    
    The bijection (i, j) ↔ (i, j+1) converts between conventions.
    See `SchurBasics.skewYoungDiagram_equiv_LR` for the equivalence proof. -/
def skewYoungDiagram (lam mu : NPartition N) : Finset (Fin N × ℕ) :=
  lam.youngDiagram \ mu.youngDiagram

/-- Membership in a skew Young diagram: (i, j) ∈ Y(λ/μ) iff μ_i ≤ j < λ_i.
    This is the 0-indexed version of the textbook condition μ_i < j ≤ λ_i. -/
theorem mem_skewYoungDiagram {lam mu : NPartition N} {c : Fin N × ℕ} :
    c ∈ skewYoungDiagram lam mu ↔ mu.parts c.1 ≤ c.2 ∧ c.2 < lam.parts c.1 := by
  simp only [skewYoungDiagram, Finset.mem_sdiff, mem_youngDiagram]
  constructor
  · intro ⟨hlt, hnotmem⟩
    exact ⟨Nat.not_lt.mp hnotmem, hlt⟩
  · intro ⟨hle, hlt⟩
    exact ⟨hlt, Nat.not_lt.mpr hle⟩

/-- Decidability of membership in skew Young diagram -/
instance skewYoungDiagram_decidableMem (lam mu : NPartition N) :
    DecidablePred (· ∈ skewYoungDiagram lam mu) := fun c =>
  decidable_of_iff (mu.parts c.1 ≤ c.2 ∧ c.2 < lam.parts c.1) mem_skewYoungDiagram.symm
/-! ## Row and Column Partitions

Special partitions consisting of a single row or column, used in the
Pieri rules and connections to symmetric functions. These are moved from
PieriJacobiTrudi.lean as part of the consolidation effort. -/


/-- The row partition (n, 0, 0, ..., 0) with n boxes in the first row.
    This is the partition corresponding to h_n (complete homogeneous symmetric polynomial).
    Requires N > 0 to have at least one row. -/
def rowPartition (N : ℕ) (n : ℕ) (_hN : 0 < N) : NPartition N where
  parts := fun i => if i.val = 0 then n else 0
  antitone := by
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
  antitone := by
    intro i j hij
    simp only
    by_cases hi : i.val < n
    · by_cases hj : j.val < n
      · simp [hi, hj]
      · simp [hi, hj]
    · by_cases hj : j.val < n
      · omega -- i.val >= n but j.val < n contradicts i ≤ j
      · simp [hi, hj]
/-! ## Transpose of a partition

The transpose of a partition λ is denoted λᵗ and satisfies:
(λᵗ)ᵢ = |{j : λⱼ ≥ i+1}| for each i.

Since we work with fixed-length tuples, we define a predicate `IsTranspose`
that captures when two tuples represent transpose partitions. -/


/-- The transpose of a partition.
    See Exercise exe.pars.transpose in the source.
    The transpose λᵗ satisfies: (λᵗ)ᵢ = |{j : λⱼ ≥ i+1}| for each i.
    The length of the transpose equals the first (largest) part of λ. -/
noncomputable def transpose (μ : NPartition N) (hN : 0 < N) : NPartition (μ.parts ⟨0, hN⟩) where
  parts := fun i => (Finset.univ.filter fun j : Fin N => i.val + 1 ≤ μ.parts j).card
  antitone := by
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

end NPartition

/-! ## Namespace aliases for migration

NOTE: The aliases below are commented out because they conflict with existing local
`NPartition` definitions in MonomialSymmetric.lean and PieriJacobiTrudi.lean.
To migrate a file to use the shared definition:
1. Import this file
2. Remove the local `structure NPartition` definition
3. Uncomment the appropriate alias below, OR use `open _root_.NPartition`

-- namespace AlgComb.SymmetricFunctions
-- abbrev NPartition := _root_.NPartition
-- end AlgComb.SymmetricFunctions

-- Note: We don't create a `SymmetricFunctions.NPartition` alias here because
-- PieriJacobiTrudi.lean already defines its own `SymmetricFunctions.NPartition`
-- structure. Migration of PieriJacobiTrudi.lean is tracked separately.
-/

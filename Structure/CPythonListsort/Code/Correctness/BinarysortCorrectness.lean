/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean -/

module

public import Def.CPythonListsort.Code.Assembly.BinarysortSafety.Part2
public import Def.CPythonListsort.Code.Assembly.Order.Part4
public import Def.CPythonListsort.Code.Correctness.SortSliceRange
public import Mathlib.Data.List.InsertIdx
public import Def.CPythonListsort.Code.Correctness.BinarysortCorrectness
/-!
# Functional correctness of `binarysort`

This file proves correctness of the reviewed binary-insertion transcription on
occurrence-carrying keys.  The proof is about the same traced execution covered
by `binarysort_safe`: raw functional correctness is identified with that result
through exact erasure, rather than through a second sorting implementation.
-/
public section




namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

variable {beta kappa rho : Type*}

/-! ## Upper-bound search semantics -/

structure BinarySearchSemanticPost
    (cmp : BoolComparator kappa) (slice : SortSlice kappa rho)
    (base : Nat) (pivot : SortSliceEntry kappa rho) (ok : Nat)
    (result : BinarySearchResult) : Prop where
  rangeStop : base + ok ≤ slice.entries.size
  fuel : result.fuelExhausted = false
  positionLe : result.position ≤ ok
  beforeFalse : ∀ i (hi : i < result.position),
    cmp pivot.key (slice.entries[base + i]'(by
      exact lt_of_lt_of_le
        (Nat.add_lt_add_left (lt_of_lt_of_le hi positionLe) base)
        rangeStop)).key = false
  afterTrue : ∀ i (_ : result.position ≤ i) (hi : i < ok),
    cmp pivot.key (slice.entries[base + i]'(by
      exact lt_of_lt_of_le (Nat.add_lt_add_left hi base) rangeStop)).key = true

end CPythonListsort

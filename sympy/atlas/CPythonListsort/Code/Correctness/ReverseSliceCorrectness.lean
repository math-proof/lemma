/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ReverseSliceCorrectness.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.ReverseSliceSafety

/-!
# Exact correctness of slice reversal

This file connects the executable `reverse_slice` transcription to a reusable
mathematical operation on half-open array ranges.  The specification retains
the prefix and suffix verbatim and reverses exactly the selected middle.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

namespace ReverseRangeSpec

/-- Replace the half-open range `[start, stop)` by its reversal. -/
def reverseRangeEntries (xs : Array α) (start stop : Nat) : Array α :=
  (xs.extract 0 start ++ (xs.extract start stop).reverse) ++
    xs.extract stop xs.size

private def ReverseRangeLoopInvariant
    (original current : Array α) (start stop i j : Nat) : Prop :=
  current.size = original.size ∧
    start ≤ i ∧ i ≤ stop ∧ start ≤ j ∧ j < stop ∧
    i + j + 1 = start + stop ∧
    ∀ k, current[k]? =
      if i ≤ k ∧ k ≤ j then original[k]?
      else (ReverseRangeSpec.reverseRangeEntries original start stop)[k]?

/-- Public exactness packet for the genuinely traced two-physical-phase
execution.  `safety` is the existing reviewed safety/erasure certificate;
the remaining fields identify its result with the mathematical reversal. -/
structure SortsliceReverseCorrectnessPost
    (before : SortSlice κ ν) (valuesPresent : Bool) (base : Int) (n : Nat)
    (result : ReverseSliceResult κ ν) : Prop where
  safety : ReverseSliceSafetyPost before valuesPresent base n result
  entriesEq :
    result.slice.entries =
      ReverseRangeSpec.reverseRangeEntries before.entries base.toNat
        (base.toNat + n)
  prefixMiddleSuffix :
    result.slice.entries.toList =
      before.entries.toList.take base.toNat ++
        (before.entries.toList.drop base.toNat |>.take n).reverse ++
          before.entries.toList.drop (base.toNat + n)
  wholeEntries : result.slice.entries.toList.Perm before.entries.toList
  beforeFrame :
    ∀ k, k < base.toNat → result.slice.entries[k]? = before.entries[k]?
  afterFrame :
    ∀ k, base.toNat + n ≤ k →
      result.slice.entries[k]? = before.entries[k]?
  involutiveExecution :
    ∃ second,
      sortsliceReverse? result.slice base n = some second ∧
        second.fuelExhausted = false ∧
        second.slice = before

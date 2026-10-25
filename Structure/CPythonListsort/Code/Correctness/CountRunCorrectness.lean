/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/CountRunCorrectness.lean -/

import Def.CPythonListsort.Code.Assembly.CountRunSafety.Part3
import Def.CPythonListsort.Code.Assembly.Order.Part4
import Structure.CPythonListsort.Code.Correctness.ReverseSliceCorrectness
import Def.CPythonListsort.Code.Correctness.SortSliceRange
import Def.CPythonListsort.Code.Correctness.DescendingRunNormalization
import Def.CPythonListsort.Code.Correctness.DescendingRunInvariant.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Correctness.ReverseRangeSupport
import Def.CPythonListsort.Code.Correctness.ScanRemainder.Part3
import Def.CPythonListsort.Code.Correctness.CountRunCorrectness
/-!
# Functional correctness of `count_run`

This file proves that the actual bounded `countRun?` transcription returns a
nonempty sorted run, preserves whole key/payload entries, and preserves the
origin order of comparator-equivalent occurrences.  The public theorem is
tied to `countRunTraced?` through the reviewed `countRun_safe` exact-erasure
certificate; no second run detector is substituted for the transcribed one.

The descending case follows CPython's two-level reversal literally.  Equal
blocks are reversed as the scan discovers them, the final equal block is
reversed at the boundary, and then the complete descending prefix is
reversed.  Thus the temporary order inside equal blocks is not exposed by the
public postcondition.
-/


namespace CPythonListsort

universe u v w x

variable {alpha : Type u} {nu : Type v}

variable {beta : Type w} {rho : Type x}

/-- Public semantic packet for one successful invocation of `count_run`.

`entryPermutation` mentions whole key/payload entries.  `stable` separately
mentions the occurrence-carrying key projection.  `frame` uses the shared
range-frame vocabulary consumed by run-formation correctness. -/
structure CountRunCorrectnessPost
    (lt : BoolComparator alpha)
    (state : MergeState (Occurrence alpha) nu)
    (before : SortSlice (Occurrence alpha) nu)
    (base : Int) (nremaining : Nat)
    (result : CountRunResult (Occurrence alpha) nu) : Prop where
  safety : CountRunSafetyPost state before base nremaining result
  lengthBounds : 1 <= result.length ∧ result.length <= nremaining
  minimumLength : nremaining = 1 ∨ 2 ≤ result.length
  sorted :
    Sorted (occurrenceComparator lt)
      (sortSliceRangeKeys result.slice base.toNat result.length)
  stable :
    StableOccurrencePermutation lt
      (sortSliceRangeKeys before base.toNat result.length).toList
      (sortSliceRangeKeys result.slice base.toNat result.length).toList
  entryPermutation :
    (sortSliceRangeEntries result.slice base.toNat result.length).toList.Perm
      (sortSliceRangeEntries before base.toNat result.length).toList
  frame :
    SortSlice.EqualOutsideRange before result.slice base.toNat result.length

/-- The functional part of `CountRunCorrectnessPost`, separated internally so
it can be established from the raw evaluator before the traced safety witness
is identified through exact erasure. -/
structure CountRunSemanticPost
    (lt : BoolComparator alpha)
    (before : SortSlice (Occurrence alpha) nu)
    (start nremaining : Nat)
    (result : CountRunResult (Occurrence alpha) nu) : Prop where
  fuel : result.fuelExhausted = false
  lengthBounds : 1 ≤ result.length ∧ result.length ≤ nremaining
  minimumLength : nremaining = 1 ∨ 2 ≤ result.length
  sorted :
    Sorted (occurrenceComparator lt)
      (sortSliceRangeKeys result.slice start result.length)
  stable :
    StableOccurrencePermutation lt
      (sortSliceRangeKeys before start result.length).toList
      (sortSliceRangeKeys result.slice start result.length).toList
  entryPermutation :
    (sortSliceRangeEntries result.slice start result.length).toList.Perm
      (sortSliceRangeEntries before start result.length).toList
  frame :
    SortSlice.EqualOutsideRange before result.slice start result.length

structure AscendingCorrectnessPost
    (lt : BoolComparator alpha)
    (slice : SortSlice (Occurrence alpha) nu)
    (start n nremaining : Nat)
    (result : AscendingScanResult) : Prop where
  fuel : result.fuelExhausted = false
  lengthBounds : n ≤ result.length ∧ result.length ≤ nremaining
  sorted :
    Sorted (occurrenceComparator lt)
      (sortSliceRangeKeys slice start result.length)
  stoppedByDecrease :
    result.length < nremaining ->
      ∃ previous next,
        slice.read? (Int.ofNat start + Int.ofNat (result.length - 1)) =
            some previous ∧
          slice.read? (Int.ofNat start + Int.ofNat result.length) =
            some next ∧
          occurrenceComparator lt next.key previous.key = true

structure ReverseLastEqualCorrectnessPost
    (before : SortSlice beta rho) (start n neq : Nat)
    (result : ReverseEqualResult beta rho) : Prop where
  resultEq :
    reverseLastEqual? before (Int.ofNat start) n neq = some result
  fuel : result.fuelExhausted = false
  entries :
    (sortSliceRangeEntries result.slice start n).toList =
      DescendingRunSpec.reverseSuffix
        (sortSliceRangeEntries before start n).toList (neq + 1)
  keys :
    (sortSliceRangeKeys result.slice start n).toList =
      DescendingRunSpec.reverseSuffix
        (sortSliceRangeKeys before start n).toList (neq + 1)
  frame : SortSlice.EqualOutsideRange before result.slice start n

structure DescendingMachineInvariant
    (lt : BoolComparator alpha)
    (source current : SortSlice (Occurrence alpha) nu)
    (start n neq : Nat) : Prop where
  frame : SortSlice.EqualOutsideRange source current start n
  keys :
    DescendingRunSpec.Invariant lt
      (sortSliceRangeKeys source start n).toList
      (sortSliceRangeKeys current start n).toList (neq + 1)
  entries :
    (DescendingRunSpec.normalize
      (sortSliceRangeEntries current start n).toList (neq + 1)).Perm
        (sortSliceRangeEntries source start n).toList

structure DescendingScanCorrectnessPost
    (lt : BoolComparator alpha)
    (source : SortSlice (Occurrence alpha) nu)
    (start n nremaining neq : Nat)
    (result : DescendingScanResult (Occurrence alpha) nu) : Prop where
  fuel : result.fuelExhausted = false
  lengthBounds : n ≤ result.length ∧ result.length ≤ nremaining
  invariant :
    DescendingMachineInvariant lt source result.slice start result.length
      result.equalTail

structure ExactReverseRangePost
    (before : SortSlice beta rho) (start count : Nat)
    (result : ReverseSliceResult beta rho) : Prop where
  resultEq :
    sortsliceReverse? before (Int.ofNat start) count = some result
  fuel : result.fuelExhausted = false
  entries :
    (sortSliceRangeEntries result.slice start count).toList =
      (sortSliceRangeEntries before start count).toList.reverse
  keys :
    (sortSliceRangeKeys result.slice start count).toList =
      (sortSliceRangeKeys before start count).toList.reverse
  frame : SortSlice.EqualOutsideRange before result.slice start count

end CPythonListsort

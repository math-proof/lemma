/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeLoInvariant.lean -/

import Def.CPythonListsort.Code.Assembly.GallopCorrectness
import Structure.CPythonListsort.Code.Assembly.MergeLoSafety.Part4
import Structure.CPythonListsort.Code.Correctness.MergeSemanticPre
import Def.CPythonListsort.Code.Correctness.MergeMovementCorrectness.Part2
import Def.CPythonListsort.Code.Correctness.SortSliceRange
import Def.CPythonListsort.Code.Correctness.StableMerge
import Def.CPythonListsort.Code.Correctness.MergeLoInvariant.Part2
/-!
# Semantic invariant for `merge_lo`

The reviewed safety invariant describes cursor geometry and storage validity.
This separate correctness invariant fixes immutable snapshots of the two
trimmed input runs and relates the emitted prefix, the live temporary suffix,
and the live main-data suffix to one shared stable-merge target.  Keeping this
layer separate prevents correctness-only order hypotheses from leaking into
the arbitrary-comparator safety theorem.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Functional invariant of every live `merge_lo` machine.

The decomposition is deliberately stated against immutable whole-entry lists.
It therefore pins key/payload pairing as well as sortedness and stability.
`lastStrict` is the correctness form of the trimmed right-end sentinel used by
the `na = 1` tail. -/
structure MergeLoSemanticMachineInvariant
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu)
    (machine : MergeLoMachine (Occurrence alpha) nu) : Prop where
  safety : MergeLoMachineInvariant (mergeLoAllocated call).state call.na
    (call.ssb + Int.ofNat call.nb) machine
  comparator : machine.state.key_compare = occurrenceComparator lt
  leftCount : machine.na ≤ call.na
  rightCount : machine.nb ≤ call.nb
  leftPositive : 0 < machine.na
  tempActive :
    MergeLoTempSuffixMatches machine.state.a (mergeLoLeftEntries call)
      machine.aPos machine.na
  mainActive :
    MergeLoMainSuffixMatches machine.state.data (mergeLoRightEntries call)
      machine.bPos (call.nb - machine.nb) machine.nb
  emittedTarget :
    mergeLoEmittedEntries call machine =
      (mergeLoTargetEntries lt call).take (mergeLoEmittedCount call machine)
  remainingTarget :
    stableEntryMerge lt
        ((mergeLoLeftEntries call).drop machine.aPos)
        ((mergeLoRightEntries call).drop (call.nb - machine.nb)) =
      (mergeLoTargetEntries lt call).drop (mergeLoEmittedCount call machine)
  frame :
    SortSlice.EqualOutsideRange call.state.data machine.state.data
      call.ssa.toNat (call.na + call.nb)
  lastStrict : machine.nb > 0 →
    ∃ lastLeft lastRight,
      mergeLoTempRead? machine.state.a
          (machine.aPos + machine.na - 1) = some lastLeft ∧
      machine.state.data.read?
          (machine.bPos + Int.ofNat (machine.nb - 1)) = some lastRight ∧
      lt lastRight.key.value lastLeft.key.value = true

/-! ## Terminal extraction -/

/-- Exact semantic output carried by either successful terminal helper. -/
structure MergeLoSemanticOutput
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu)
    (state : MergeState (Occurrence alpha) nu) : Prop where
  exactRange :
    (sortSliceRangeEntries state.data call.ssa.toNat
      (call.na + call.nb)).toList = mergeLoTargetEntries lt call
  frame : SortSlice.EqualOutsideRange call.state.data state.data
    call.ssa.toNat (call.na + call.nb)

end CPythonListsort

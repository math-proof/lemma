/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean -/

import Def.CPythonListsort.Code.Assembly.ReverseSliceSafety.Part2
import Def.CPythonListsort.Code.Transcription.CountRun.Part4
import Theorem.CPythonListsort.Code.Assembly.CountRunSafety.Part6
/-!
# `count_run` safety

The evaluator below mirrors the reviewed `count_run` transcription while
producing its trace compositionally.  The Lean instrumentation reads the
previous entry and then the next entry; its comparator orientation and control
branch match CPython's `IF_NEXT_SMALLER`, without making a claim about C operand
evaluation order.  Every operational-equivalence-block, prefix, and whole-run
reversal delegates to the traced `sortslice_reverse` evaluator proved safe in
`ReverseSliceSafety`.

As in the v1 transcription, `BoolComparator` is total.  CPython's comparator
error/failure return path is therefore outside this model; the safety theorem is
for every total Boolean comparator, including inconsistent ones.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Public safety certificate for natural-run detection. -/
structure CountRunSafetyPost
    (state : MergeState κ ν) (before : SortSlice κ ν) (base : Int)
    (nremaining : Nat) (result : CountRunResult κ ν) : Prop where
  resultEq :
    (countRunTraced? state before base nremaining).result = some result
  resultFuel : result.fuelExhausted = false
  traceFuel :
    (countRunTraced? state before base nremaining).trace.fuelExhausted = false
  accessesInBounds :
    (countRunTraced? state before base nremaining).trace.allAccessesInBounds
  tempAccessesLive :
    (countRunTraced? state before base nremaining).trace.tempPayloadAccessesLive
  noPushes :
    (countRunTraced? state before base nremaining).trace.pushDepths = []
  exactErasure :
    (countRunTraced? state before base nremaining).erase =
      countRun? state before base nremaining
  valuesMode :
    SortSlice.ValuesModeInvariant state.a.hasValues result.slice
  sizeEq : result.slice.entries.size = before.entries.size
  lengthBounds : 1 ≤ result.length ∧ result.length ≤ nremaining

end CPythonListsort

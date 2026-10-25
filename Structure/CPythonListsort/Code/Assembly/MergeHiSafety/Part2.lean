/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety
import Def.CPythonListsort.Code.Assembly.MergeHiSafety.Part2
/-!
# `merge_hi` traced execution and safety

This module instruments the right-to-left merge directly.  Its evaluator does
not run `mergeHi?` and attach a second, decorative trace: every state transition
is produced by the typed operation that emits its access events.  The three
`memcpy` paths retain their exact source call-site tag and distinct-backing
permit, main-data block movement uses the overlap-safe traced `memmove`, and
temporary gallops read their live storage through `GallopKeySource.temporary`.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

namespace MergeHiStableFrame

namespace MergeHiStorageFrame

namespace MergeHiCursorInvariant

/-- Internal inductive postcondition shared by terminal paths and the phase
driver.  The reference computation is the corresponding reviewed untraced
fragment, so erasure stays lockstep throughout the induction. -/
structure MergeHiCorePost
    (origin : MergeState κ ν) (request : Nat)
    (execution : TraceResult (MergeHiResult κ ν))
    (reference : Option (MergeHiResult κ ν))
    (result : MergeHiResult κ ν) : Prop where
  resultEq : execution.result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceSafe : MovementTraceSafe execution
  exactErasure : execution.erase = reference
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  requestFits : request ≤ result.state.alloced.toNat
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  stableFrame : MergeHiStableFrame origin result.state
  storageFrame : MergeHiStorageFrame origin result.state

end MergeHiCursorInvariant
end MergeHiStorageFrame
end MergeHiStableFrame
end CPythonListsort

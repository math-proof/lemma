/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTracePrimitives.lean -/

import Def.CPythonListsort.Code.Assembly.MergeMemcpyProvenance
import Theorem.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part3
/-!
# Typed trace support for merge movement

The merge transcriptions keep the main list in `MergeState.data` and the
shorter run in `MergeState.a`.  `SortSlice`'s two-store movement API cannot be
used directly for that pair because temporary storage has a distinct carrier,
an explicit live/released backing state, and possibly-uninitialized cells.

This module supplies the common traced movement layer used by both merge
directions.  Every access goes through a state-derived wrapper from
`AccessTrace`; in particular, callers cannot manufacture the temporary backing
or either extent.  Bulk `memcpy` executors retain a classified call-site tag,
its exact direction, and its distinct-backing certificate at every recursive
call.  Key accesses for the complete range precede the optional synchronized-
values phase, which is selected solely by `state.a.hasValues`.
-/


namespace CPythonListsort

universe u v

open SortSlice

namespace TempRangeInBounds

namespace MergeMovementFrame

namespace MovementAccessOnly

namespace AccessTrace.HasAccess

/-! ## Public aggregate bulk contracts -/

structure MainToTempMemcpyPost
    (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
    (state result : MergeState κ ν) (tempDst mainSrc : Int) : Prop where
  success :
    (mainToTempMemcpyTraced? site permit count state tempDst mainSrc).result =
      some result
  traceSafe :
    MovementTraceSafe
      (mainToTempMemcpyTraced? site permit count state tempDst mainSrc)
  exactErasure :
    (mainToTempMemcpyTraced? site permit count state tempDst mainSrc).erase =
      mainToTempMemcpy? count state tempDst mainSrc
  frame : MergeMovementFrame state result
  tempInvariant : TempStorageInv result.a result.alloced
  tempLive : result.a.Live
  valuesMode : SortSlice.ValuesModeInvariant result.a.hasValues result.data
  initialized : TempRangeInitialized result.a tempDst count
  tempValuesMode : TempRangeValuesMode result.a tempDst count
  provenance : site.backings.Distinct
  /-- The complete generic `sortslice_memcpy` safety boundary used by this
  classified call site: distinct backing is admissible, while an overlapping
  same-backing request is rejected with an empty trace. -/
  provenanceContract : MergeMemcpyCallsiteProvenanceContract κ ν
  phaseOrder :
    (mainToTempMemcpyTraced? site permit count state tempDst mainSrc).trace.accesses =
      (mainToTempKeysTraced? site permit count state tempDst mainSrc).trace.accesses ++
        (if state.a.hasValues then
          (mainToTempValuesPhaseTraced? site permit count state tempDst
            mainSrc).trace.accesses
        else [])
  inputKeyEvent : 0 < count →
    (mainToTempMemcpyTraced? site permit count state tempDst
      mainSrc).trace.HasAccess .read .inputKeys
  tempWriteEvent : 0 < count →
    (mainToTempMemcpyTraced? site permit count state tempDst
      mainSrc).trace.HasTempAccess .write
  synchronizedValuesEvent : 0 < count → state.a.hasValues = true →
    (mainToTempMemcpyTraced? site permit count state tempDst
      mainSrc).trace.HasAccess .read .synchronizedValues
  nonempty : 0 < count →
    (mainToTempMemcpyTraced? site permit count state tempDst
      mainSrc).trace.accesses ≠ []

structure TempToMainMemcpyPost
    (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
    (state result : MergeState κ ν) (mainDst tempSrc : Int) : Prop where
  success :
    (tempToMainMemcpyTraced? site permit count state mainDst tempSrc).result =
      some result
  traceSafe :
    MovementTraceSafe
      (tempToMainMemcpyTraced? site permit count state mainDst tempSrc)
  exactErasure :
    (tempToMainMemcpyTraced? site permit count state mainDst tempSrc).erase =
      tempToMainMemcpy? count state mainDst tempSrc
  frame : MergeMovementFrame state result
  tempInvariant : TempStorageInv result.a result.alloced
  tempLive : result.a.Live
  valuesMode : SortSlice.ValuesModeInvariant result.a.hasValues result.data
  initialized : TempRangeInitialized result.a tempSrc count
  tempValuesMode : TempRangeValuesMode result.a tempSrc count
  provenance : site.backings.Distinct
  /-- The complete generic `sortslice_memcpy` safety boundary used by this
  classified call site: distinct backing is admissible, while an overlapping
  same-backing request is rejected with an empty trace. -/
  provenanceContract : MergeMemcpyCallsiteProvenanceContract κ ν
  phaseOrder :
    (tempToMainMemcpyTraced? site permit count state mainDst tempSrc).trace.accesses =
      (tempToMainKeysTraced? site permit count state mainDst tempSrc).trace.accesses ++
        (if state.a.hasValues then
          (tempToMainValuesPhaseTraced? site permit count state mainDst
            tempSrc).trace.accesses
        else [])
  tempReadEvent : 0 < count →
    (tempToMainMemcpyTraced? site permit count state mainDst
      tempSrc).trace.HasTempAccess .read
  inputKeyEvent : 0 < count →
    (tempToMainMemcpyTraced? site permit count state mainDst
      tempSrc).trace.HasAccess .write .inputKeys
  synchronizedValuesEvent : 0 < count → state.a.hasValues = true →
    (tempToMainMemcpyTraced? site permit count state mainDst
      tempSrc).trace.HasAccess .write .synchronizedValues
  nonempty : 0 < count →
    (tempToMainMemcpyTraced? site permit count state mainDst
      tempSrc).trace.accesses ≠ []

end AccessTrace.HasAccess
end MovementAccessOnly
end MergeMovementFrame
end TempRangeInBounds
end CPythonListsort

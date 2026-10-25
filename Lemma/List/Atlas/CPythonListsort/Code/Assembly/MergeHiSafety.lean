import Mathlib
import sympy.Basic
import Theorem.CPythonListsort.Code.Assembly.MergeHiSafety.Part5
open CPythonListsort CPythonListsort.MergeHiStableFrame CPythonListsort.MergeHiStorageFrame CPythonListsort.MergeHiCursorInvariant


namespace CPythonListsort

/--
[erase_mergeHiTraceOption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma erase_mergeHiTraceOption
  {κ : Type u}
  {ν : Type v}
  {value : Option α} :
-- imply
  (mergeHiTraceOption value).erase = value := by
-- proof
  cases value <;> rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_pure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_pure (value : α) :
  MergeHiMemoryEventFree (TraceResult.pure value) :=
⟨rfl, rfl⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_failure :
  MergeHiMemoryEventFree (TraceResult.failure : TraceResult α) :=
⟨rfl, rfl⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_map (current : TraceResult α)
  (transform : α → β) (hcurrent : MergeHiMemoryEventFree current) :
  MergeHiMemoryEventFree (current.map transform) :=
  hcurrent

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_bind (current : TraceResult α)
  (next : α → TraceResult β) (hcurrent : MergeHiMemoryEventFree current)
  (hnext : ∀ value, MergeHiMemoryEventFree (next value)) :
  MergeHiMemoryEventFree (current.bind next) := by
  exact
    ⟨TraceResult.memoryEvents_bind_eq_nil current next hcurrent.1
      (fun value => (hnext value).1),
      TraceResult.policyEvents_bind_eq_nil current next hcurrent.2
        (fun value => (hnext value).2)⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_markFuelExhausted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_markFuelExhausted
  (current : TraceResult α) (hcurrent : MergeHiMemoryEventFree current) :
  MergeHiMemoryEventFree current.markFuelExhausted := by
  simpa [MergeHiMemoryEventFree, TraceResult.markFuelExhausted,
    AccessTrace.compose, AccessTrace.exhausted] using hcurrent

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_sourceRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_sourceRead
  (source : GallopKeySource κ ν) (index : Int) :
  MergeHiMemoryEventFree (source.readTraced? index) := by
  simp [MergeHiMemoryEventFree, GallopKeySource.trace_readTraced,
    AccessTrace.singletonAccess]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_tempRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_tempRead
  (storage : TempStorage κ ν) (index : Int) :
  MergeHiMemoryEventFree (TraceResult.tempPayloadRead? storage index) := by
  unfold MergeHiMemoryEventFree
  rw [TraceResult.trace_tempPayloadRead]
  exact ⟨rfl, rfl⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_tempWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_tempWrite
  (storage : TempStorage κ ν) (index : Int)
  (entry : SortSliceEntry κ ν) :
  MergeHiMemoryEventFree
    (TraceResult.tempPayloadWrite? storage index entry) :=
⟨rfl, rfl⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_keyRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_keyRead
  (slice : SortSlice κ ν) (index : Int) :
  MergeHiMemoryEventFree (TraceResult.sortSliceKeysRead? slice index) :=
⟨rfl, rfl⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_valueRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_valueRead
  (slice : SortSlice κ ν) (index : Int) :
  MergeHiMemoryEventFree (TraceResult.sortSliceValuesRead? slice index) :=
⟨rfl, rfl⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_keyWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_keyWrite
  (slice : SortSlice κ ν) (index : Int) (entry : SortSliceEntry κ ν) :
  MergeHiMemoryEventFree
    (TraceResult.sortSliceKeysWrite? slice index entry) :=
⟨rfl, rfl⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_valueWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_valueWrite
  (slice : SortSlice κ ν) (index : Int) (entry : SortSliceEntry κ ν) :
  MergeHiMemoryEventFree
    (TraceResult.sortSliceValuesWrite? slice index entry) :=
⟨rfl, rfl⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_copyKeys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_copyKeys
  (destination source : SortSlice κ ν) (dst src : Int) :
  MergeHiMemoryEventFree
    (SortSlice.copyKeysFromTraced? destination source dst src) := by
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_keyRead _ _
  · intro entry
    exact mergeHiMemoryEventFree_keyWrite _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_copyValues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_copyValues
  (destination source : SortSlice κ ν) (dst src : Int) :
  MergeHiMemoryEventFree
    (SortSlice.copyValuesFromTraced? destination source dst src) := by
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_valueRead _ _
  · intro entry
    exact mergeHiMemoryEventFree_valueWrite _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_mainToTempKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_mainToTempKey
  (state : MergeState κ ν) (tempDst mainSrc : Int) :
  MergeHiMemoryEventFree (mainToTempKeyTraced? state tempDst mainSrc) := by
  unfold mainToTempKeyTraced?
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_keyRead _ _
  · intro entry
    apply mergeHiMemoryEventFree_map
    exact mergeHiMemoryEventFree_tempWrite _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_mainToTempValues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_mainToTempValues
  (state : MergeState κ ν) (tempDst mainSrc : Int) :
  MergeHiMemoryEventFree (mainToTempValuesTraced? state tempDst mainSrc) := by
  unfold mainToTempValuesTraced?
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_valueRead _ _
  · intro entry
    apply mergeHiMemoryEventFree_map
    exact mergeHiMemoryEventFree_tempWrite _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_tempToMainKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_tempToMainKey
  (state : MergeState κ ν) (mainDst tempSrc : Int) :
  MergeHiMemoryEventFree (tempToMainKeyTraced? state mainDst tempSrc) := by
  unfold tempToMainKeyTraced?
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_tempRead _ _
  · intro entry
    apply mergeHiMemoryEventFree_map
    exact mergeHiMemoryEventFree_keyWrite _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_tempToMainValues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_tempToMainValues
  (state : MergeState κ ν) (mainDst tempSrc : Int) :
  MergeHiMemoryEventFree (tempToMainValuesTraced? state mainDst tempSrc) := by
  unfold tempToMainValuesTraced?
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_tempRead _ _
  · intro entry
    apply mergeHiMemoryEventFree_map
    exact mergeHiMemoryEventFree_valueWrite _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_tempToMainCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_tempToMainCell
  (state : MergeState κ ν) (mainDst tempSrc : Int) :
  MergeHiMemoryEventFree (tempToMainCellTraced? state mainDst tempSrc) := by
  unfold tempToMainCellTraced?
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_tempToMainKey _ _ _
  · intro keyResult
    split
    · exact mergeHiMemoryEventFree_tempToMainValues _ _ _
    · exact mergeHiMemoryEventFree_pure _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_mainToTempKeys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_mainToTempKeys
  (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
  (state : MergeState κ ν) (tempDst mainSrc : Int) :
  MergeHiMemoryEventFree
    (mainToTempKeysTraced? site permit count state tempDst mainSrc) := by
  induction count generalizing state tempDst mainSrc with
  | zero => exact mergeHiMemoryEventFree_pure _
  | succ count ih =>
    simp only [mainToTempKeysTraced?]
    apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_mainToTempKey _ _ _
    · intro nextState
      exact ih _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_mainToTempValuesPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_mainToTempValuesPhase
  (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
  (state : MergeState κ ν) (tempDst mainSrc : Int) :
  MergeHiMemoryEventFree
    (mainToTempValuesPhaseTraced? site permit count state tempDst mainSrc) := by
  induction count generalizing state tempDst mainSrc with
  | zero => exact mergeHiMemoryEventFree_pure _
  | succ count ih =>
    simp only [mainToTempValuesPhaseTraced?]
    apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_mainToTempValues _ _ _
    · intro nextState
      exact ih _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_mainToTempMemcpy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_mainToTempMemcpy
  (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
  (state : MergeState κ ν) (tempDst mainSrc : Int) :
  MergeHiMemoryEventFree
    (mainToTempMemcpyTraced? site permit count state tempDst mainSrc) := by
  unfold mainToTempMemcpyTraced?
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_mainToTempKeys _ _ _ _ _ _
  · intro keyResult
    split
    · exact mergeHiMemoryEventFree_mainToTempValuesPhase _ _ _ _ _ _
    · exact mergeHiMemoryEventFree_pure _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_tempToMainKeys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_tempToMainKeys
  (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
  (state : MergeState κ ν) (mainDst tempSrc : Int) :
  MergeHiMemoryEventFree
    (tempToMainKeysTraced? site permit count state mainDst tempSrc) := by
  induction count generalizing state mainDst tempSrc with
  | zero => exact mergeHiMemoryEventFree_pure _
  | succ count ih =>
    simp only [tempToMainKeysTraced?]
    apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_tempToMainKey _ _ _
    · intro nextState
      exact ih _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_tempToMainValuesPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_tempToMainValuesPhase
  (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
  (state : MergeState κ ν) (mainDst tempSrc : Int) :
  MergeHiMemoryEventFree
    (tempToMainValuesPhaseTraced? site permit count state mainDst tempSrc) := by
  induction count generalizing state mainDst tempSrc with
  | zero => exact mergeHiMemoryEventFree_pure _
  | succ count ih =>
    simp only [tempToMainValuesPhaseTraced?]
    apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_tempToMainValues _ _ _
    · intro nextState
      exact ih _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_tempToMainMemcpy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_tempToMainMemcpy
  (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
  (state : MergeState κ ν) (mainDst tempSrc : Int) :
  MergeHiMemoryEventFree
    (tempToMainMemcpyTraced? site permit count state mainDst tempSrc) := by
  unfold tempToMainMemcpyTraced?
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_tempToMainKeys _ _ _ _ _ _
  · intro keyResult
    split
    · exact mergeHiMemoryEventFree_tempToMainValuesPhase _ _ _ _ _ _
    · exact mergeHiMemoryEventFree_pure _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_memmoveForwardKeys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_memmoveForwardKeys
  (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
  MergeHiMemoryEventFree
    (SortSlice.memmoveForwardKeysTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact mergeHiMemoryEventFree_pure _
  | succ count ih =>
    simp only [SortSlice.memmoveForwardKeysTraced?]
    apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_copyKeys _ _ _ _
    · intro updated
      exact ih _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_memmoveForwardValues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_memmoveForwardValues
  (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
  MergeHiMemoryEventFree
    (SortSlice.memmoveForwardValuesTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact mergeHiMemoryEventFree_pure _
  | succ count ih =>
    simp only [SortSlice.memmoveForwardValuesTraced?]
    apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_copyValues _ _ _ _
    · intro updated
      exact ih _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_memmoveBackwardKeys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_memmoveBackwardKeys
  (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
  MergeHiMemoryEventFree
    (SortSlice.memmoveBackwardKeysTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact mergeHiMemoryEventFree_pure _
  | succ count ih =>
    simp only [SortSlice.memmoveBackwardKeysTraced?]
    apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_copyKeys _ _ _ _
    · intro updated
      exact ih _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_memmoveBackwardValues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_memmoveBackwardValues
  (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
  MergeHiMemoryEventFree
    (SortSlice.memmoveBackwardValuesTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact mergeHiMemoryEventFree_pure _
  | succ count ih =>
    simp only [SortSlice.memmoveBackwardValuesTraced?]
    apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_copyValues _ _ _ _
    · intro updated
      exact ih _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_memmove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_memmove
  (valuesPresent : Bool) (slice : SortSlice κ ν)
  (dst src : Int) (count : Nat) :
  MergeHiMemoryEventFree
    (SortSlice.memmoveTraced? valuesPresent slice dst src count) := by
  unfold SortSlice.memmoveTraced?
  split
  · apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_memmoveForwardKeys _ _ _ _
    · intro keyResult
      split
      · exact mergeHiMemoryEventFree_memmoveForwardValues _ _ _ _
      · exact mergeHiMemoryEventFree_pure _
  · apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_memmoveBackwardKeys _ _ _ _
    · intro keyResult
      split
      · exact mergeHiMemoryEventFree_memmoveBackwardValues _ _ _ _
      · exact mergeHiMemoryEventFree_pure _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_mainDataMemmove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_mainDataMemmove
  (state : MergeState κ ν) (dst src : Int) (count : Nat) :
  MergeHiMemoryEventFree (mainDataMemmoveTraced? state dst src count) := by
  unfold mainDataMemmoveTraced?
  apply mergeHiMemoryEventFree_map
  exact mergeHiMemoryEventFree_memmove _ _ _ _ _
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_leftRightExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_leftRightExponential
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (hint maxOffset lastOffset offset : Nat) :
  MergeHiMemoryEventFree
    (gallopLeftRightExponentialTraced? fuel lt source key hint maxOffset
      lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
    by_cases hfuel : offset < maxOffset <;>
      simp [gallopLeftRightExponentialTraced?, MergeHiMemoryEventFree,
        hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
    simp only [gallopLeftRightExponentialTraced?]
    split
    · apply mergeHiMemoryEventFree_bind
      · exact mergeHiMemoryEventFree_sourceRead _ _
      · intro entry
        split
        · split
          · exact ih _ _
          · exact mergeHiMemoryEventFree_failure
        · exact mergeHiMemoryEventFree_pure _
    · exact mergeHiMemoryEventFree_pure _
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_leftLeftExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_leftLeftExponential
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (hint maxOffset lastOffset offset : Nat) :
  MergeHiMemoryEventFree
    (gallopLeftLeftExponentialTraced? fuel lt source key hint maxOffset
      lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
    by_cases hfuel : offset < maxOffset <;>
      simp [gallopLeftLeftExponentialTraced?, MergeHiMemoryEventFree,
        hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
    simp only [gallopLeftLeftExponentialTraced?]
    split
    · apply mergeHiMemoryEventFree_bind
      · exact mergeHiMemoryEventFree_sourceRead _ _
      · intro entry
        split
        · exact mergeHiMemoryEventFree_pure _
        · split
          · exact ih _ _
          · exact mergeHiMemoryEventFree_failure
    · exact mergeHiMemoryEventFree_pure _
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_rightLeftExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_rightLeftExponential
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (hint maxOffset lastOffset offset : Nat) :
  MergeHiMemoryEventFree
    (gallopRightLeftExponentialTraced? fuel lt source key hint maxOffset
      lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
    by_cases hfuel : offset < maxOffset <;>
      simp [gallopRightLeftExponentialTraced?, MergeHiMemoryEventFree,
        hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
    simp only [gallopRightLeftExponentialTraced?]
    split
    · apply mergeHiMemoryEventFree_bind
      · exact mergeHiMemoryEventFree_sourceRead _ _
      · intro entry
        split
        · split
          · exact ih _ _
          · exact mergeHiMemoryEventFree_failure
        · exact mergeHiMemoryEventFree_pure _
    · exact mergeHiMemoryEventFree_pure _
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_rightRightExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_rightRightExponential
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (hint maxOffset lastOffset offset : Nat) :
  MergeHiMemoryEventFree
    (gallopRightRightExponentialTraced? fuel lt source key hint maxOffset
      lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
    by_cases hfuel : offset < maxOffset <;>
      simp [gallopRightRightExponentialTraced?, MergeHiMemoryEventFree,
        hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
    simp only [gallopRightRightExponentialTraced?]
    split
    · apply mergeHiMemoryEventFree_bind
      · exact mergeHiMemoryEventFree_sourceRead _ _
      · intro entry
        split
        · exact mergeHiMemoryEventFree_pure _
        · split
          · exact ih _ _
          · exact mergeHiMemoryEventFree_failure
    · exact mergeHiMemoryEventFree_pure _
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_leftBinary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_leftBinary
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (lower upper : Nat) :
  MergeHiMemoryEventFree
    (gallopLeftBinaryTraced? fuel lt source key lower upper) := by
  induction fuel generalizing lower upper with
  | zero =>
    by_cases hfuel : lower < upper <;>
      simp [gallopLeftBinaryTraced?, MergeHiMemoryEventFree, hfuel] <;>
        (constructor <;> rfl)
  | succ fuel ih =>
    simp only [gallopLeftBinaryTraced?]
    split
    · apply mergeHiMemoryEventFree_bind
      · exact mergeHiMemoryEventFree_sourceRead _ _
      · intro entry
        split
        · exact ih _ _
        · exact ih _ _
    · exact mergeHiMemoryEventFree_pure _
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_rightBinary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_rightBinary
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (lower upper : Nat) :
  MergeHiMemoryEventFree
    (gallopRightBinaryTraced? fuel lt source key lower upper) := by
  induction fuel generalizing lower upper with
  | zero =>
    by_cases hfuel : lower < upper <;>
      simp [gallopRightBinaryTraced?, MergeHiMemoryEventFree, hfuel] <;>
        (constructor <;> rfl)
  | succ fuel ih =>
    simp only [gallopRightBinaryTraced?]
    split
    · apply mergeHiMemoryEventFree_bind
      · exact mergeHiMemoryEventFree_sourceRead _ _
      · intro entry
        split
        · exact ih _ _
        · exact ih _ _
    · exact mergeHiMemoryEventFree_pure _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_finishLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_finishLeft
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (n : Nat) (lastOffset upperOffset : Int)
  (exponentialFuelExhausted : Bool) :
  MergeHiMemoryEventFree
    (finishGallopLeftTraced? fuel lt source key n lastOffset upperOffset
      exponentialFuelExhausted) := by
  unfold finishGallopLeftTraced?
  split
  · dsimp only
    split
    · split
      · constructor <;> rfl
      · exact mergeHiMemoryEventFree_leftBinary _ _ _ _ _ _
    · exact mergeHiMemoryEventFree_failure
  · exact mergeHiMemoryEventFree_failure

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_finishRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_finishRight
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (n : Nat) (lastOffset upperOffset : Int)
  (exponentialFuelExhausted : Bool) :
  MergeHiMemoryEventFree
    (finishGallopRightTraced? fuel lt source key n lastOffset upperOffset
      exponentialFuelExhausted) := by
  unfold finishGallopRightTraced?
  split
  · dsimp only
    split
    · split
      · constructor <;> rfl
      · exact mergeHiMemoryEventFree_rightBinary _ _ _ _ _ _
    · exact mergeHiMemoryEventFree_failure
  · exact mergeHiMemoryEventFree_failure

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_gallopLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_gallopLeft
  (state : MergeState κ ν) (source : GallopKeySource κ ν)
  (key : κ) (n hint : Nat) :
  MergeHiMemoryEventFree (gallopLeftTraced? state source key n hint) := by
  unfold gallopLeftTraced?
  split
  · apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_sourceRead _ _
    · intro hinted
      split
      · apply mergeHiMemoryEventFree_bind
        · exact mergeHiMemoryEventFree_leftRightExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact mergeHiMemoryEventFree_finishLeft _ _ _ _ _ _ _ _
      · apply mergeHiMemoryEventFree_bind
        · exact mergeHiMemoryEventFree_leftLeftExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact mergeHiMemoryEventFree_finishLeft _ _ _ _ _ _ _ _
  · exact mergeHiMemoryEventFree_failure

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_gallopRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_gallopRight
  (state : MergeState κ ν) (source : GallopKeySource κ ν)
  (key : κ) (n hint : Nat) :
  MergeHiMemoryEventFree (gallopRightTraced? state source key n hint) := by
  unfold gallopRightTraced?
  split
  · apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_sourceRead _ _
    · intro hinted
      split
      · apply mergeHiMemoryEventFree_bind
        · exact mergeHiMemoryEventFree_rightLeftExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact mergeHiMemoryEventFree_finishRight _ _ _ _ _ _ _ _
      · apply mergeHiMemoryEventFree_bind
        · exact mergeHiMemoryEventFree_rightRightExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact mergeHiMemoryEventFree_finishRight _ _ _ _ _ _ _ _
  · exact mergeHiMemoryEventFree_failure

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_copyFrom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_copyFrom
  (valuesPresent : Bool) (destination source : SortSlice κ ν)
  (dst src : Int) :
  MergeHiMemoryEventFree
    (SortSlice.copyFromTraced? valuesPresent destination source dst src) := by
  unfold SortSlice.copyFromTraced?
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_copyKeys _ _ _ _
  · intro keyResult
    split
    · exact mergeHiMemoryEventFree_copyValues _ _ _ _
    · exact mergeHiMemoryEventFree_pure _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_mainDataCopyDecr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_mainDataCopyDecr
  (state : MergeState κ ν) (dst src : Int) :
  MergeHiMemoryEventFree (mainDataCopyDecrTraced? state dst src) := by
  unfold mainDataCopyDecrTraced? SortSlice.copyDecrTraced?
    SortSlice.copyFromDecrTraced?
  apply mergeHiMemoryEventFree_map
  exact mergeHiMemoryEventFree_copyFrom _ _ _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_copyDataDecr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_copyDataDecr
  (state : MergeState κ ν) (dst src : Int) :
  MergeHiMemoryEventFree (mergeHiCopyDataDecrTraced? state dst src) :=
mergeHiMemoryEventFree_mainDataCopyDecr _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_copyTempDecr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_copyTempDecr
  (state : MergeState κ ν) (dst src : Int) :
  MergeHiMemoryEventFree (mergeHiCopyTempDecrTraced? state dst src) := by
  unfold mergeHiCopyTempDecrTraced?
  apply mergeHiMemoryEventFree_map
  exact mergeHiMemoryEventFree_tempToMainCell _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_moveABlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_moveABlock
  (cursor : MergeHiCursor κ ν) (count : Nat) :
  MergeHiMemoryEventFree (mergeHiMoveABlockTraced? cursor count) := by
  unfold mergeHiMoveABlockTraced?
  split
  · exact mergeHiMemoryEventFree_pure _
  · dsimp only
    apply mergeHiMemoryEventFree_map
    exact mergeHiMemoryEventFree_mainDataMemmove _ _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_moveBBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_moveBBlock
  (cursor : MergeHiCursor κ ν) (count : Nat) :
  MergeHiMemoryEventFree (mergeHiMoveBBlockTraced? cursor count) := by
  unfold mergeHiMoveBBlockTraced?
  split
  · exact mergeHiMemoryEventFree_pure _
  · dsimp only
    apply mergeHiMemoryEventFree_map
    exact mergeHiMemoryEventFree_tempToMainMemcpy _ _ _ _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_fuelExhausted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_fuelExhausted
  (cursor : MergeHiCursor κ ν) :
  MergeHiMemoryEventFree (mergeHiFuelExhaustedTraced cursor) := by
  apply mergeHiMemoryEventFree_markFuelExhausted
  exact mergeHiMemoryEventFree_pure _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_succeed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_succeed
  (cursor : MergeHiCursor κ ν) :
  MergeHiMemoryEventFree (mergeHiSucceedTraced? cursor) := by
  unfold mergeHiSucceedTraced?
  apply mergeHiMemoryEventFree_map
  split
  · exact mergeHiMemoryEventFree_pure _
  · exact mergeHiMemoryEventFree_tempToMainMemcpy _ _ _ _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_copyA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_copyA
  (cursor : MergeHiCursor κ ν) :
  MergeHiMemoryEventFree (mergeHiCopyATraced? cursor) := by
  unfold mergeHiCopyATraced?
  split
  · dsimp only
    apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_mainDataMemmove _ _ _ _
    · intro state
      apply mergeHiMemoryEventFree_map
      exact mergeHiMemoryEventFree_tempToMainCell _ _ _
  · exact mergeHiMemoryEventFree_failure

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_traceOption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_traceOption (value : Option α) :
  MergeHiMemoryEventFree (mergeHiTraceOption value) := by
  cases value
  · exact mergeHiMemoryEventFree_failure
  · exact mergeHiMemoryEventFree_pure _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_gallopBFinish](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_gallopBFinish
  (afterB : MergeHiCursor κ ν) (aCount bCount : Nat)
  (movedB : MergeHiCursor κ ν)
  (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
  (hnext : ∀ cursor, MergeHiMemoryEventFree (next cursor)) :
  MergeHiMemoryEventFree
    (mergeHiGallopBFinishTraced? afterB aCount bCount movedB next) := by
  unfold mergeHiGallopBFinishTraced?
  split
  · exact hnext _
  · apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_copyDataDecr _ _ _
    · intro copiedA
      dsimp only
      split
      · exact hnext _
      · split
        · exact hnext _
        · exact hnext _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_gallopBAfter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_gallopBAfter
  (afterB : MergeHiCursor κ ν) (aCount : Nat) (gallopB : GallopResult)
  (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
  (hnext : ∀ cursor, MergeHiMemoryEventFree (next cursor)) :
  MergeHiMemoryEventFree
    (mergeHiGallopBAfterTraced? afterB aCount gallopB next) := by
  unfold mergeHiGallopBAfterTraced?
  split
  · exact mergeHiMemoryEventFree_fuelExhausted _
  · dsimp only
    apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_moveBBlock _ _
    · intro movedB
      exact mergeHiMemoryEventFree_gallopBFinish _ _ _ _ _ hnext

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_gallopB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_gallopB
  (afterB : MergeHiCursor κ ν) (aCount : Nat)
  (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
  (hnext : ∀ cursor, MergeHiMemoryEventFree (next cursor)) :
  MergeHiMemoryEventFree (mergeHiGallopBTraced? afterB aCount next) := by
  unfold mergeHiGallopBTraced?
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_keyRead _ _
  · intro left
    apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_traceOption _
    · intro _temp
      apply mergeHiMemoryEventFree_bind
      · exact mergeHiMemoryEventFree_gallopLeft _ _ _ _ _
      · intro gallopB
        exact mergeHiMemoryEventFree_gallopBAfter _ _ _ _ hnext

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_gallopRoundFinish](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_gallopRoundFinish
  (movedA : MergeHiCursor κ ν) (aCount : Nat)
  (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
  (hnext : ∀ cursor, MergeHiMemoryEventFree (next cursor)) :
  MergeHiMemoryEventFree
    (mergeHiGallopRoundFinishTraced? movedA aCount next) := by
  unfold mergeHiGallopRoundFinishTraced?
  split
  · exact hnext _
  · apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_copyTempDecr _ _ _
    · intro copiedB
      dsimp only
      split
      · exact hnext _
      · exact mergeHiMemoryEventFree_gallopB _ _ _ hnext

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_gallopRoundAfter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_gallopRoundAfter
  (cursor : MergeHiCursor κ ν) (minGallop : PySSize)
  (state : MergeState κ ν) (gallopA : GallopResult)
  (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
  (hnext : ∀ cursor, MergeHiMemoryEventFree (next cursor)) :
  MergeHiMemoryEventFree
    (mergeHiGallopRoundAfterTraced? cursor minGallop state gallopA next) := by
  unfold mergeHiGallopRoundAfterTraced?
  split
  · exact mergeHiMemoryEventFree_fuelExhausted _
  · dsimp only
    apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_moveABlock _ _
    · intro movedA
      exact mergeHiMemoryEventFree_gallopRoundFinish _ _ _ hnext

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_gallopRound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_gallopRound
  (cursor : MergeHiCursor κ ν)
  (next : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
  (hnext : ∀ cursor, MergeHiMemoryEventFree (next cursor)) :
  MergeHiMemoryEventFree (mergeHiGallopRoundTraced? cursor next) := by
  unfold mergeHiGallopRoundTraced?
  dsimp only
  apply mergeHiMemoryEventFree_bind
  · exact mergeHiMemoryEventFree_tempRead _ _
  · intro right
    apply mergeHiMemoryEventFree_bind
    · exact mergeHiMemoryEventFree_gallopRight _ _ _ _ _
    · intro gallopA
      exact mergeHiMemoryEventFree_gallopRoundAfter _ _ _ _ _ hnext

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemoryEventFree_loop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMemoryEventFree_loop
  (fuel : Nat) (cursor : MergeHiCursor κ ν) :
  MergeHiMemoryEventFree (mergeHiLoopTraced? fuel cursor) := by
  induction fuel generalizing cursor with
  | zero =>
    simp only [mergeHiLoopTraced?]
    split
    · exact mergeHiMemoryEventFree_succeed _
    · split
      · exact mergeHiMemoryEventFree_copyA _
      · exact mergeHiMemoryEventFree_fuelExhausted _
  | succ fuel ih =>
    simp only [mergeHiLoopTraced?]
    split
    · exact mergeHiMemoryEventFree_succeed _
    · split
      · exact mergeHiMemoryEventFree_copyA _
      · split
        · apply mergeHiMemoryEventFree_bind
          · exact mergeHiMemoryEventFree_tempRead _ _
          · intro right
            apply mergeHiMemoryEventFree_bind
            · exact mergeHiMemoryEventFree_keyRead _ _
            · intro left
              split
              · apply mergeHiMemoryEventFree_bind
                · exact mergeHiMemoryEventFree_copyDataDecr _ _ _
                · intro copied
                  exact ih _
              · apply mergeHiMemoryEventFree_bind
                · exact mergeHiMemoryEventFree_copyTempDecr _ _ _
                · intro copied
                  exact ih _
        · exact mergeHiMemoryEventFree_gallopRound _ _ (fun _ => ih _)

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiTraced_topLevelEvents_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiTraced_topLevelEvents_empty
  (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat) :
  MergeHiMemoryEventFree (mergeHiTraced? state ssa ssb na nb) := by
  unfold mergeHiTraced?
  split
  · dsimp only
    split
    · exact mergeHiMemoryEventFree_pure _
    · apply mergeHiMemoryEventFree_bind
      · exact mergeHiMemoryEventFree_mainToTempMemcpy _ _ _ _ _ _
      · intro copiedTemp
        apply mergeHiMemoryEventFree_bind
        · exact mergeHiMemoryEventFree_copyDataDecr _ _ _
        · intro copiedFirst
          exact mergeHiMemoryEventFree_loop _ _
    · apply mergeHiMemoryEventFree_bind
      · exact mergeHiMemoryEventFree_mainToTempMemcpy _ _ _ _ _ _
      · intro copiedTemp
        apply mergeHiMemoryEventFree_bind
        · exact mergeHiMemoryEventFree_copyDataDecr _ _ _
        · intro copiedFirst
          exact mergeHiMemoryEventFree_loop _ _
  · exact mergeHiMemoryEventFree_failure

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiTraced_memoryEvents_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma mergeHiTraced_memoryEvents_empty
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {ssa ssb : Int}
  {na nb : Nat} :
-- imply
  (mergeHiTraced? state ssa ssb na nb).trace.memoryEvents = [] :=
-- proof
  (mergeHiTraced_topLevelEvents_empty state ssa ssb na nb).1

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiTraced_policyEvents_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma mergeHiTraced_policyEvents_empty
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {ssa ssb : Int}
  {na nb : Nat} :
-- imply
  (mergeHiTraced? state ssa ssb na nb).trace.policyEvents = [] :=
-- proof
  (mergeHiTraced_topLevelEvents_empty state ssa ssb na nb).2

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[optionMap_eq_bindSome](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma optionMap_eq_bindSome (value : Option α) (f : α → β) :
  value.map f = value.bind fun item => some (f item) := by
  cases value <;> rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeTempRead_eq_mergeHiTempRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma mergeTempRead_eq_mergeHiTempRead
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {index : Int} :
-- imply
  mergeTempRead? storage index = mergeHiTempRead? storage index := by
-- proof
  by_cases hindex : 0 ≤ index
  · cases hcell : storage.cells[index.toNat]? with
    | none => simp [mergeTempRead?, mergeHiTempRead?, hindex, hcell]
    | some cell =>
      cases cell <;> simp [mergeTempRead?, mergeHiTempRead?, hindex, hcell]
  · simp [mergeTempRead?, mergeHiTempRead?, hindex]

end CPythonListsort

namespace CPythonListsort

/--
[mergeTempWrite_eq_mergeHiTempWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma mergeTempWrite_eq_mergeHiTempWrite
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν} :
-- imply
  mergeTempWrite? storage index entry = mergeHiTempWrite? storage index entry := by
-- proof
  by_cases hindex : 0 ≤ index
  · by_cases hbounds : index.toNat < storage.cells.size <;>
    simp [mergeTempWrite?, mergeHiTempWrite?, hindex, hbounds,
      Array.setIfInBounds]
  · simp [mergeTempWrite?, mergeHiTempWrite?, hindex]

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempCell_eq_mergeHiCopyDataToTemp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma mainToTempCell_eq_mergeHiCopyDataToTemp
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {dst src : Int} :
-- imply
  mainToTempCell? state dst src = mergeHiCopyDataToTemp? state dst src := by
-- proof
  simp [mainToTempCell?, mergeHiCopyDataToTemp?]

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainCell_eq_mergeHiCopyTempToData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma tempToMainCell_eq_mergeHiCopyTempToData
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {dst src : Int} :
-- imply
  tempToMainCell? state dst src = mergeHiCopyTempToData? state dst src := by
-- proof
  simp [tempToMainCell?, mergeHiCopyTempToData?]

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempMemcpy_eq_mergeHiMemcpyDataToTemp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma mainToTempMemcpy_eq_mergeHiMemcpyDataToTemp
  {κ : Type u}
  {ν : Type v}
  {site : MergeHiMemcpyCallsite}
  {count : Nat}
  {state : MergeState κ ν}
  {dst src : Int}
-- given
  (hDirection : site.backings = { destination := .temporary, source := .main }) :
-- imply
  mainToTempMemcpy? count state dst src = mergeHiMemcpyDataToTemp? site hDirection count state dst src := by
-- proof
  induction count generalizing state dst src with
  | zero => rfl
  | succ count ih =>
    simp [mainToTempMemcpy?, mergeHiMemcpyDataToTemp?, ih]

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainMemcpy_eq_mergeHiMemcpyTempToData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma tempToMainMemcpy_eq_mergeHiMemcpyTempToData
  {κ : Type u}
  {ν : Type v}
  {site : MergeHiMemcpyCallsite}
  {count : Nat}
  {state : MergeState κ ν}
  {dst src : Int}
-- given
  (hDirection : site.backings = { destination := .main, source := .temporary }) :
-- imply
  tempToMainMemcpy? count state dst src = mergeHiMemcpyTempToData? site hDirection count state dst src := by
-- proof
  induction count generalizing state dst src with
  | zero => rfl
  | succ count ih =>
    simp [tempToMainMemcpy?, mergeHiMemcpyTempToData?, ih]

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeHiCopyDataDecrTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma erase_mergeHiCopyDataDecrTraced
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {dst src : Int} :
-- imply
  (mergeHiCopyDataDecrTraced? state dst src).erase = mergeHiCopyDataDecr? state dst src :=
-- proof
erase_mainDataCopyDecrTraced state dst src

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeHiCopyTempDecrTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma erase_mergeHiCopyTempDecrTraced
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {dst src : Int} :
-- imply
  (mergeHiCopyTempDecrTraced? state dst src).erase = mergeHiCopyTempDecr? state dst src := by
-- proof
  rw [mergeHiCopyTempDecrTraced?, TraceResult.erase_map,
    erase_tempToMainCellTraced, tempToMainCell_eq_mergeHiCopyTempToData]
  cases hcopy : mergeHiCopyTempToData? state dst src <;>
    simp [mergeHiCopyTempDecr?, hcopy]

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeHiMoveABlockTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma erase_mergeHiMoveABlockTraced
  {κ : Type u}
  {ν : Type v}
  {cursor : MergeHiCursor κ ν}
  {count : Nat} :
-- imply
  (mergeHiMoveABlockTraced? cursor count).erase = mergeHiMoveABlock? cursor count := by
-- proof
  unfold mergeHiMoveABlockTraced? mergeHiMoveABlock?
  by_cases hcount : count = 0
  · simp [hcount]
  · simp only [hcount, ↓reduceIte, TraceResult.erase_map,
    erase_mainDataMemmoveTraced]
    exact optionMap_eq_bindSome _ _

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeHiMoveBBlockTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma erase_mergeHiMoveBBlockTraced
  {κ : Type u}
  {ν : Type v}
  {cursor : MergeHiCursor κ ν}
  {count : Nat} :
-- imply
  (mergeHiMoveBBlockTraced? cursor count).erase = mergeHiMoveBBlock? cursor count := by
-- proof
  unfold mergeHiMoveBBlockTraced? mergeHiMoveBBlock?
  by_cases hcount : count = 0
  · simp [hcount]
  · simp only [hcount, ↓reduceIte, TraceResult.erase_map,
    erase_tempToMainMemcpyTraced]
    rw [tempToMainMemcpy_eq_mergeHiMemcpyTempToData .gallopTempToData rfl]
    exact optionMap_eq_bindSome _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[erase_mergeHiGallopBFinishTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma erase_mergeHiGallopBFinishTraced
  (afterB : MergeHiCursor κ ν) (aCount bCount : Nat)
  (movedB : MergeHiCursor κ ν)
  (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
  (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
  (hnext : ∀ cursor, (nextTraced cursor).erase = next cursor) :
  (mergeHiGallopBFinishTraced? afterB aCount bCount movedB
    nextTraced).erase =
    mergeHiGallopBFinish? afterB aCount bCount movedB next := by
  unfold mergeHiGallopBFinishTraced? mergeHiGallopBFinish?
  by_cases hterminal : movedB.nb = 0 ∨ movedB.nb = 1
  · simp [hterminal, hnext]
  · simp only [hterminal, ↓reduceIte, TraceResult.erase_bind,
    erase_mergeHiCopyDataDecrTraced]
    apply Option.bind_congr
    intro copiedA _hcopied
    split
    · exact hnext _
    · split <;> exact hnext _

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeHiFuelExhaustedTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma erase_mergeHiFuelExhaustedTraced
  {κ : Type u}
  {ν : Type v}
  {cursor : MergeHiCursor κ ν} :
-- imply
  (mergeHiFuelExhaustedTraced cursor).erase = some (mergeHiFuelExhausted cursor) := by
-- proof
  simp [mergeHiFuelExhaustedTraced]

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeHiSucceedTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma erase_mergeHiSucceedTraced
  {κ : Type u}
  {ν : Type v}
  {cursor : MergeHiCursor κ ν} :
-- imply
  (mergeHiSucceedTraced? cursor).erase = mergeHiSucceed? cursor := by
-- proof
  unfold mergeHiSucceedTraced? mergeHiSucceed?
  by_cases hnb : cursor.nb = 0
  · simp [hnb]
  · simp only [hnb, ↓reduceIte, TraceResult.erase_map,
    erase_tempToMainMemcpyTraced]
    rw [tempToMainMemcpy_eq_mergeHiMemcpyTempToData .finalTempToData rfl]
    cases hcopy : mergeHiMemcpyTempToData? .finalTempToData rfl cursor.nb
      cursor.state (cursor.dest - Int.ofNat (cursor.nb - 1)) 0 <;>
      simp

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeHiCopyATraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma erase_mergeHiCopyATraced
  {κ : Type u}
  {ν : Type v}
  {cursor : MergeHiCursor κ ν} :
-- imply
  (mergeHiCopyATraced? cursor).erase = mergeHiCopyA? cursor := by
-- proof
  unfold mergeHiCopyATraced? mergeHiCopyA?
  simp only [mergeDataMemmove_eq]
  by_cases htail : cursor.nb = 1 ∧ 0 < cursor.na
  · rw [if_pos htail, if_pos htail, TraceResult.erase_bind,
    erase_mainDataMemmoveTraced]
    simp only [mainDataMemmove?, TraceResult.erase_map,
      erase_tempToMainCellTraced,
      tempToMainCell_eq_mergeHiCopyTempToData]
    cases hmove : cursor.state.data.memmove?
      (cursor.dest + (1 - Int.ofNat cursor.na))
      (cursor.ssa + (1 - Int.ofNat cursor.na)) cursor.na with
    | none => simp
    | some data =>
      exact optionMap_eq_bindSome _ _
  · rw [if_neg htail, if_neg htail]
    rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[erase_mergeHiTemporaryGallopLeft_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
gallop whenever prefix materialization succeeds.  No safety premise is needed:
outside the signed gallop domain both evaluators reject by the same guard. -/
private lemma erase_mergeHiTemporaryGallopLeft_of_eq_some
  (state : MergeState κ ν) (count hint : Nat)
  (slice : SortSlice κ ν) (key : κ)
  (hSlice : initializedTempPrefix? state.a count = some slice) :
  (gallopLeftTraced? state (.temporary state.a 0) key count hint).erase =
    gallopLeft? state slice 0 key count hint := by
  rw [erase_gallopLeftTraced]
  by_cases hInput : 0 < count ∧ hint < count ∧ count ≤ PY_SSIZE_T_MAX
  · exact gallopLeftFromSource_eq_slice_of_ssize state
    (.temporary state.a 0) slice 0 key count hint
    (initializedTempPrefix_agreesWithSlice_of_eq_some state.a count slice
      hSlice)
    hInput.1 hInput.2.1 hInput.2.2
  · unfold gallopLeftFromSource? gallopLeft?
    simp only [hInput, if_false]

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiTemporary_validRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma mergeHiTemporary_validRange
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {count : Nat}
-- given
  (hbound : count ≤ storage.cells.size)
  (hinitialized : TempRangeInitialized storage 0 count) :
-- imply
  (GallopKeySource.temporary storage 0).ValidRange count := by
-- proof
  refine ⟨by simp [GallopKeySource.base], ?_, ?_⟩
  · simpa [GallopKeySource.base, GallopKeySource.extent,
    Int.ofNat_eq_natCast] using Int.ofNat_le.mpr hbound
  · intro i hi
    obtain ⟨entry, hentry⟩ := hinitialized i hi
    refine ⟨entry, ?_⟩
    rw [erase_mergeTempRead] at hentry
    simpa [GallopKeySource.read?, GallopKeySource.base,
      mergeTempRead?, Int.ofNat_eq_natCast] using hentry

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiMain_validRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma mergeHiMain_validRange
  {κ : Type u}
  {ν : Type v}
  {slice : SortSlice κ ν}
  {base : Int}
  {count : Nat}
-- given
  (hbase : 0 ≤ base)
  (hend : base + Int.ofNat count ≤ Int.ofNat slice.entries.size) :
-- imply
  (GallopKeySource.main slice base).ValidRange count := by
-- proof
  refine ⟨hbase, ?_, ?_⟩
  · simpa [GallopKeySource.base, GallopKeySource.extent] using hend
  · intro i hi
    have hiInt : Int.ofNat i < Int.ofNat count := Int.ofNat_lt.mpr hi
    have hindex : SortSlice.IndexInBounds slice
      (base + Int.ofNat i) := by
      constructor
      · exact add_nonneg hbase (Int.natCast_nonneg i)
      · exact lt_of_lt_of_le (by simpa [add_comm] using
        (add_lt_add_left hiInt base)) hend
    rcases SortSlice.read_eq_some_of_indexInBounds slice _ hindex with
      ⟨entry, hentry⟩
    exact ⟨entry, by
      simpa [GallopKeySource.read?, GallopKeySource.base] using hentry⟩

end CPythonListsort

namespace CPythonListsort.MergeHiStableFrame

/--
[refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma refl
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν} :
-- imply
  MergeHiStableFrame state state := by
-- proof
  constructor <;> rfl

end CPythonListsort.MergeHiStableFrame

namespace CPythonListsort.MergeHiStableFrame

/--
[trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma trans
  {κ : Type u}
  {ν : Type v}
  {first second third : MergeState κ ν}
-- given
  (hfirst : MergeHiStableFrame first second)
  (hsecond : MergeHiStableFrame second third) :
-- imply
  MergeHiStableFrame first third := by
-- proof
  constructor
  · exact hsecond.listlen.trans hfirst.listlen
  · exact hsecond.basekeys.trans hfirst.basekeys
  · exact hsecond.dataSize.trans hfirst.dataSize
  · exact hsecond.tempValuesMode.trans hfirst.tempValuesMode
  · exact hsecond.pending.trans hfirst.pending
  · exact hsecond.comparator.trans hfirst.comparator
  · exact hsecond.mrCurrent.trans hfirst.mrCurrent
  · exact hsecond.mrE.trans hfirst.mrE
  · exact hsecond.mrMask.trans hfirst.mrMask

end CPythonListsort.MergeHiStableFrame

namespace CPythonListsort.MergeHiStableFrame

/--
[of_movement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma of_movement
  {κ : Type u}
  {ν : Type v}
  {before after : MergeState κ ν}
-- given
  (hframe : MergeMovementFrame before after) :
-- imply
  MergeHiStableFrame before after := by
-- proof
  exact
    { listlen := hframe.listlen
      basekeys := hframe.basekeys
      dataSize := hframe.dataSize
      tempValuesMode := hframe.tempValuesMode
      pending := hframe.pending
      comparator := hframe.comparator
      mrCurrent := hframe.mrCurrent
      mrE := hframe.mrE
      mrMask := hframe.mrMask }

end CPythonListsort.MergeHiStableFrame

namespace CPythonListsort.MergeHiStableFrame

/--
[of_getmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma of_getmem
  {κ : Type u}
  {ν : Type v}
  {before : MergeState κ ν}
  {need : PySSize}
  {post : MergeGetmemStoragePost before need (mergeGetmem before need)} :
-- imply
  MergeHiStableFrame before (mergeGetmem before need).state := by
-- proof
  obtain ⟨hmrCurrent, hmrE, hmrMask⟩ := post.minrun_eq
  exact
    { listlen := post.listlen_eq
      basekeys := post.basekeys_eq
      dataSize := by rw [post.data_eq]
      tempValuesMode := post.valuesMode
      pending := post.pending_eq
      comparator := post.keyCompare_eq
      mrCurrent := hmrCurrent
      mrE := hmrE
      mrMask := hmrMask }

end CPythonListsort.MergeHiStableFrame

namespace CPythonListsort.MergeHiStorageFrame

/--
[refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma refl
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν} :
-- imply
  MergeHiStorageFrame state state := by
-- proof
  constructor <;> rfl

end CPythonListsort.MergeHiStorageFrame

namespace CPythonListsort.MergeHiStorageFrame

/--
[trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma trans
  {κ : Type u}
  {ν : Type v}
  {first second third : MergeState κ ν}
-- given
  (hfirst : MergeHiStorageFrame first second)
  (hsecond : MergeHiStorageFrame second third) :
-- imply
  MergeHiStorageFrame first third := by
-- proof
  exact
    { cellsSize := hsecond.cellsSize.trans hfirst.cellsSize
      backing := hsecond.backing.trans hfirst.backing
      hasValues := hsecond.hasValues.trans hfirst.hasValues
      alloced := hsecond.alloced.trans hfirst.alloced }

end CPythonListsort.MergeHiStorageFrame

namespace CPythonListsort.MergeHiStorageFrame

/--
[of_movement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma of_movement
  {κ : Type u}
  {ν : Type v}
  {before after : MergeState κ ν}
-- given
  (hframe : MergeMovementFrame before after) :
-- imply
  MergeHiStorageFrame before after :=
-- proof
  { cellsSize := hframe.tempSize
    backing := hframe.tempBacking
    hasValues := hframe.tempValuesMode
    alloced := hframe.alloced }

end CPythonListsort.MergeHiStorageFrame

namespace CPythonListsort.MergeHiStorageFrame

/--
[physicalSlots_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma physicalSlots_eq
  {κ : Type u}
  {ν : Type v}
  {before after : MergeState κ ν}
-- given
  (hframe : MergeHiStorageFrame before after) :
-- imply
  after.a.physicalSlots = before.a.physicalSlots := by
-- proof
  simp only [TempStorage.physicalSlots, TempStorage.multiplier]
  rw [hframe.cellsSize, hframe.hasValues]

end CPythonListsort.MergeHiStorageFrame

namespace CPythonListsort.MergeHiCursorInvariant

/--
[ssaInBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma ssaInBounds
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {request : Nat}
  {cursor : MergeHiCursor κ ν}
-- given
  (h : MergeHiCursorInvariant origin request cursor)
  (hna : 0 < cursor.na) :
-- imply
  SortSlice.IndexInBounds cursor.state.data cursor.ssa := by
-- proof
  have heq := h.ssaEquation
  have hrange := h.mainRange
  have hbase := h.baseNonnegative
  have hnbNonnegative : (0 : Int) ≤ (cursor.nb : Int) :=
    Int.natCast_nonneg _
  change 0 ≤ cursor.ssa ∧
    cursor.ssa < Int.ofNat cursor.state.data.entries.size
  simp only [Int.ofNat_eq_natCast, Nat.cast_add] at heq hrange ⊢
  constructor <;> omega

end CPythonListsort.MergeHiCursorInvariant

namespace CPythonListsort.MergeHiCursorInvariant

/--
[ssbInBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma ssbInBounds
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {request : Nat}
  {cursor : MergeHiCursor κ ν}
-- given
  (h : MergeHiCursorInvariant origin request cursor)
  (hnb : 0 < cursor.nb) :
-- imply
  TempIndexInBounds cursor.state.a cursor.ssb := by
-- proof
  have heq := h.ssbEquation
  have hcapacity : (cursor.nb : Int) ≤
    (cursor.state.a.cells.size : Int) := by
    exact_mod_cast h.tempCapacity
  change 0 ≤ cursor.ssb ∧
    cursor.ssb < Int.ofNat cursor.state.a.cells.size
  simp only [Int.ofNat_eq_natCast] at heq ⊢
  constructor <;> omega

end CPythonListsort.MergeHiCursorInvariant

namespace CPythonListsort.MergeHiCursorInvariant

/--
[destInBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma destInBounds
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {request : Nat}
  {cursor : MergeHiCursor κ ν}
-- given
  (h : MergeHiCursorInvariant origin request cursor)
  (hactive : 0 < cursor.na + cursor.nb) :
-- imply
  SortSlice.IndexInBounds cursor.state.data cursor.dest := by
-- proof
  have heq := h.destEquation
  have hrange := h.mainRange
  have hbase := h.baseNonnegative
  have hsumPositive : (0 : Int) < (cursor.na + cursor.nb : Nat) := by
    exact_mod_cast hactive
  change 0 ≤ cursor.dest ∧
    cursor.dest < Int.ofNat cursor.state.data.entries.size
  simp only [Int.ofNat_eq_natCast, Nat.cast_add] at heq hrange ⊢
  constructor <;> omega

end CPythonListsort.MergeHiCursorInvariant

namespace CPythonListsort.MergeHiCursorInvariant

/--
[tempReadable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma tempReadable
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {request : Nat}
  {cursor : MergeHiCursor κ ν}
-- given
  (h : MergeHiCursorInvariant origin request cursor)
  (hnb : 0 < cursor.nb) :
-- imply
  ∃ entry, mergeTempRead? cursor.state.a cursor.ssb = some entry := by
-- proof
  have heq := h.ssbEquation
  have hindex : cursor.ssb = Int.ofNat (cursor.nb - 1) := by
    simp only [Int.ofNat_eq_natCast] at heq ⊢
    omega
  rcases h.tempValuesMode (cursor.nb - 1) (by omega) with
    ⟨entry, hread, _⟩
  rw [erase_mergeTempRead] at hread
  rw [hindex]
  exact ⟨entry, by simpa using hread⟩

end CPythonListsort.MergeHiCursorInvariant

namespace CPythonListsort.MergeHiCursorInvariant

/--
[temporaryValidRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma temporaryValidRange
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {request : Nat}
  {cursor : MergeHiCursor κ ν}
-- given
  (h : MergeHiCursorInvariant origin request cursor) :
-- imply
  (GallopKeySource.temporary cursor.state.a 0).ValidRange cursor.nb :=
-- proof
  mergeHiTemporary_validRange cursor.state.a cursor.nb h.tempCapacity
    h.tempValuesMode.initialized

end CPythonListsort.MergeHiCursorInvariant

namespace CPythonListsort.MergeHiCursorInvariant

/--
[mainValidRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma mainValidRange
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {request : Nat}
  {cursor : MergeHiCursor κ ν}
-- given
  (h : MergeHiCursorInvariant origin request cursor) :
-- imply
  (GallopKeySource.main cursor.state.data cursor.basea).ValidRange cursor.na := by
-- proof
  apply mergeHiMain_validRange cursor.state.data cursor.basea cursor.na
    h.baseNonnegative
  have hrange := h.mainRange
  simp only [Int.ofNat_eq_natCast, Nat.cast_add] at hrange ⊢
  have hnbNonnegative : (0 : Int) ≤ (cursor.nb : Int) :=
    Int.natCast_nonneg _
  omega

end CPythonListsort.MergeHiCursorInvariant

namespace CPythonListsort.MergeHiCursorInvariant

/--
[replaceState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma replaceState
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {request : Nat}
  {cursor : MergeHiCursor κ ν}
  {after : MergeState κ ν}
-- given
  (h : MergeHiCursorInvariant origin request cursor)
  (hframe : MergeMovementFrame cursor.state after)
  (htemp : after.a = cursor.state.a)
  (hmode : SortSlice.ValuesModeInvariant after.a.hasValues after.data) :
-- imply
  MergeHiCursorInvariant origin request { cursor with state := after } := by
-- proof
  exact
    { baseNonnegative := h.baseNonnegative
      ssaEquation := h.ssaEquation
      ssbEquation := h.ssbEquation
      destEquation := h.destEquation
      mainRange := by simpa only [hframe.dataSize] using h.mainRange
      leftWordBound := h.leftWordBound
      rightWordBound := h.rightWordBound
      tempCapacity := by simpa only [htemp] using h.tempCapacity
      tempValuesMode := by simpa only [htemp] using h.tempValuesMode
      tempInvariant := hframe.tempStorageInv h.tempInvariant
      tempLive := hframe.live h.tempLive
      requestFits := by simpa only [hframe.alloced] using h.requestFits
      valuesMode := hmode
      stableFrame := h.stableFrame.trans (.of_movement hframe)
      storageFrame := h.storageFrame.trans (.of_movement hframe) }

end CPythonListsort.MergeHiCursorInvariant

namespace CPythonListsort.MergeHiCursorInvariant

/--
[setMinGallop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma setMinGallop
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {request : Nat}
  {cursor : MergeHiCursor κ ν}
  {minGallop : PySSize}
-- given
  (h : MergeHiCursorInvariant origin request cursor) :
-- imply
  MergeHiCursorInvariant origin request { cursor with state := { cursor.state with min_gallop := minGallop } minGallop := minGallop } := by
-- proof
  exact
    { baseNonnegative := h.baseNonnegative
      ssaEquation := h.ssaEquation
      ssbEquation := h.ssbEquation
      destEquation := h.destEquation
      mainRange := h.mainRange
      leftWordBound := h.leftWordBound
      rightWordBound := h.rightWordBound
      tempCapacity := h.tempCapacity
      tempValuesMode := h.tempValuesMode
      tempInvariant := h.tempInvariant
      tempLive := h.tempLive
      requestFits := h.requestFits
      valuesMode := h.valuesMode
      stableFrame :=
        { listlen := h.stableFrame.listlen
          basekeys := h.stableFrame.basekeys
          dataSize := h.stableFrame.dataSize
          tempValuesMode := h.stableFrame.tempValuesMode
          pending := h.stableFrame.pending
          comparator := h.stableFrame.comparator
          mrCurrent := h.stableFrame.mrCurrent
          mrE := h.stableFrame.mrE
          mrMask := h.stableFrame.mrMask }
      storageFrame :=
        { cellsSize := h.storageFrame.cellsSize
          backing := h.storageFrame.backing
          hasValues := h.storageFrame.hasValues
          alloced := h.storageFrame.alloced } }

end CPythonListsort.MergeHiCursorInvariant

namespace CPythonListsort.MergeHiCursorInvariant

/--
[setControl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma setControl
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {request : Nat}
  {cursor : MergeHiCursor κ ν}
  {minGallop : PySSize}
  {phase : MergeHiPhase}
-- given
  (h : MergeHiCursorInvariant origin request cursor) :
-- imply
  MergeHiCursorInvariant origin request { cursor with minGallop := minGallop, phase := phase } := by
-- proof
  exact
    { baseNonnegative := h.baseNonnegative
      ssaEquation := h.ssaEquation
      ssbEquation := h.ssbEquation
      destEquation := h.destEquation
      mainRange := h.mainRange
      leftWordBound := h.leftWordBound
      rightWordBound := h.rightWordBound
      tempCapacity := h.tempCapacity
      tempValuesMode := h.tempValuesMode
      tempInvariant := h.tempInvariant
      tempLive := h.tempLive
      requestFits := h.requestFits
      valuesMode := h.valuesMode
      stableFrame := h.stableFrame
      storageFrame := h.storageFrame }

end CPythonListsort.MergeHiCursorInvariant

namespace CPythonListsort.MergeHiCursorInvariant

/--
[copyA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma copyA
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {request : Nat}
  {cursor : MergeHiCursor κ ν}
  {after : MergeState κ ν}
-- given
  (h : MergeHiCursorInvariant origin request cursor)
  (hframe : MergeMovementFrame cursor.state after)
  (htemp : after.a = cursor.state.a)
  (hmode : SortSlice.ValuesModeInvariant after.a.hasValues after.data)
  (hna : 0 < cursor.na) :
-- imply
  MergeHiCursorInvariant origin request { cursor with state := after dest := cursor.dest - 1 ssa := cursor.ssa - 1 na := cursor.na - 1 } := by
-- proof
  have hs := h.replaceState after hframe htemp hmode
  exact
    { baseNonnegative := h.baseNonnegative
      ssaEquation := by
        have heq := h.ssaEquation
        simp only [Int.ofNat_eq_natCast, Nat.cast_sub hna] at heq ⊢
        omega
      ssbEquation := h.ssbEquation
      destEquation := by
        have heq := h.destEquation
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hna]
          at heq ⊢
        omega
      mainRange := by
        have hrange := hs.mainRange
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hna]
          at hrange ⊢
        omega
      leftWordBound := (Nat.sub_le cursor.na 1).trans h.leftWordBound
      rightWordBound := h.rightWordBound
      tempCapacity := hs.tempCapacity
      tempValuesMode := hs.tempValuesMode
      tempInvariant := hs.tempInvariant
      tempLive := hs.tempLive
      requestFits := hs.requestFits
      valuesMode := hs.valuesMode
      stableFrame := hs.stableFrame
      storageFrame := hs.storageFrame }

end CPythonListsort.MergeHiCursorInvariant

namespace CPythonListsort.MergeHiCursorInvariant

/--
[copyB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma copyB
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {request : Nat}
  {cursor : MergeHiCursor κ ν}
  {after : MergeState κ ν}
-- given
  (h : MergeHiCursorInvariant origin request cursor)
  (hframe : MergeMovementFrame cursor.state after)
  (htemp : after.a = cursor.state.a)
  (hmode : SortSlice.ValuesModeInvariant after.a.hasValues after.data)
  (hnb : 0 < cursor.nb) :
-- imply
  MergeHiCursorInvariant origin request { cursor with state := after dest := cursor.dest - 1 ssb := cursor.ssb - 1 nb := cursor.nb - 1 } := by
-- proof
  have hs := h.replaceState after hframe htemp hmode
  exact
    { baseNonnegative := h.baseNonnegative
      ssaEquation := h.ssaEquation
      ssbEquation := by
        have heq := h.ssbEquation
        simp only [Int.ofNat_eq_natCast, Nat.cast_sub hnb] at heq ⊢
        omega
      destEquation := by
        have heq := h.destEquation
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hnb]
          at heq ⊢
        omega
      mainRange := by
        have hrange := hs.mainRange
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hnb]
          at hrange ⊢
        omega
      leftWordBound := h.leftWordBound
      rightWordBound := (Nat.sub_le cursor.nb 1).trans h.rightWordBound
      tempCapacity := (Nat.sub_le cursor.nb 1).trans hs.tempCapacity
      tempValuesMode := by
        change TempRangeValuesMode after.a 0 (cursor.nb - 1)
        intro offset hoffset
        exact hs.tempValuesMode offset
          (lt_of_lt_of_le hoffset (Nat.sub_le cursor.nb 1))
      tempInvariant := hs.tempInvariant
      tempLive := hs.tempLive
      requestFits := hs.requestFits
      valuesMode := hs.valuesMode
      stableFrame := hs.stableFrame
      storageFrame := hs.storageFrame }

end CPythonListsort.MergeHiCursorInvariant

namespace CPythonListsort.MergeHiCursorInvariant

/--
[copyABlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma copyABlock
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {request : Nat}
  {cursor : MergeHiCursor κ ν}
  {count : Nat}
  {after : MergeState κ ν}
-- given
  (h : MergeHiCursorInvariant origin request cursor)
  (hcount : count ≤ cursor.na)
  (hframe : MergeMovementFrame cursor.state after)
  (htemp : after.a = cursor.state.a)
  (hmode : SortSlice.ValuesModeInvariant after.a.hasValues after.data) :
-- imply
  MergeHiCursorInvariant origin request { cursor with state := after dest := cursor.dest - Int.ofNat count ssa := cursor.ssa - Int.ofNat count na := cursor.na - count } := by
-- proof
  have hs := h.replaceState after hframe htemp hmode
  exact
    { baseNonnegative := h.baseNonnegative
      ssaEquation := by
        have heq := h.ssaEquation
        simp only [Int.ofNat_eq_natCast, Nat.cast_sub hcount] at heq ⊢
        omega
      ssbEquation := h.ssbEquation
      destEquation := by
        have heq := h.destEquation
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hcount]
          at heq ⊢
        omega
      mainRange := by
        have hrange := hs.mainRange
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hcount]
          at hrange ⊢
        omega
      leftWordBound := (Nat.sub_le cursor.na count).trans h.leftWordBound
      rightWordBound := h.rightWordBound
      tempCapacity := hs.tempCapacity
      tempValuesMode := hs.tempValuesMode
      tempInvariant := hs.tempInvariant
      tempLive := hs.tempLive
      requestFits := hs.requestFits
      valuesMode := hs.valuesMode
      stableFrame := hs.stableFrame
      storageFrame := hs.storageFrame }

end CPythonListsort.MergeHiCursorInvariant

namespace CPythonListsort.MergeHiCursorInvariant

/--
[copyBBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma copyBBlock
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {request : Nat}
  {cursor : MergeHiCursor κ ν}
  {count : Nat}
  {after : MergeState κ ν}
-- given
  (h : MergeHiCursorInvariant origin request cursor)
  (hcount : count ≤ cursor.nb)
  (hframe : MergeMovementFrame cursor.state after)
  (htemp : after.a = cursor.state.a)
  (hmode : SortSlice.ValuesModeInvariant after.a.hasValues after.data) :
-- imply
  MergeHiCursorInvariant origin request { cursor with state := after dest := cursor.dest - Int.ofNat count ssb := cursor.ssb - Int.ofNat count nb := cursor.nb - count } := by
-- proof
  have hs := h.replaceState after hframe htemp hmode
  exact
    { baseNonnegative := h.baseNonnegative
      ssaEquation := h.ssaEquation
      ssbEquation := by
        have heq := h.ssbEquation
        simp only [Int.ofNat_eq_natCast, Nat.cast_sub hcount] at heq ⊢
        omega
      destEquation := by
        have heq := h.destEquation
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hcount]
          at heq ⊢
        omega
      mainRange := by
        have hrange := hs.mainRange
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hcount]
          at hrange ⊢
        omega
      leftWordBound := h.leftWordBound
      rightWordBound := (Nat.sub_le cursor.nb count).trans h.rightWordBound
      tempCapacity := (Nat.sub_le cursor.nb count).trans hs.tempCapacity
      tempValuesMode := by
        change TempRangeValuesMode after.a 0 (cursor.nb - count)
        intro offset hoffset
        exact hs.tempValuesMode offset
          (lt_of_lt_of_le hoffset (Nat.sub_le cursor.nb count))
      tempInvariant := hs.tempInvariant
      tempLive := hs.tempLive
      requestFits := hs.requestFits
      valuesMode := hs.valuesMode
      stableFrame := hs.stableFrame
      storageFrame := hs.storageFrame }

end CPythonListsort.MergeHiCursorInvariant

namespace CPythonListsort

/--
[mergeHiNbZeroHedgeRegressionCursor_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma mergeHiNbZeroHedgeRegressionCursor_invariant
  {κ : Type u}
  {ν : Type v} :
-- imply
  MergeHiCursorInvariant mergeHiNbZeroHedgeRegressionState 2 mergeHiNbZeroHedgeRegressionCursor := by
-- proof
  refine
    { baseNonnegative := by decide
      ssaEquation := by decide
      ssbEquation := by decide
      destEquation := by decide
      mainRange := by decide
      leftWordBound := by decide
      rightWordBound := by decide
      tempCapacity := by decide
      tempValuesMode := ?_
      tempInvariant := by
        have hcapacity : 4 ≤ MERGESTATE_TEMP_SIZE := by decide
        simpa [mergeHiNbZeroHedgeRegressionCursor,
          mergeHiNbZeroHedgeRegressionState, TempStorageInv,
          TempStorage.multiplier] using hcapacity
      tempLive := by
        simp [mergeHiNbZeroHedgeRegressionCursor,
          mergeHiNbZeroHedgeRegressionState, TempStorage.Live]
      requestFits := by decide
      valuesMode := ?_
      stableFrame := ?_
      storageFrame := ?_ }
  · intro index hindex
    have hindex' : index < 2 := by
      simpa [mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · intro index hindex
    have hindex' : index < 3 := by
      simpa [mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · simpa [mergeHiNbZeroHedgeRegressionCursor] using
    MergeHiStableFrame.refl mergeHiNbZeroHedgeRegressionState
  · simpa [mergeHiNbZeroHedgeRegressionCursor] using
    MergeHiStorageFrame.refl mergeHiNbZeroHedgeRegressionState

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiNbZeroHedgeStrictControlCursor_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma mergeHiNbZeroHedgeStrictControlCursor_invariant
  {κ : Type u}
  {ν : Type v} :
-- imply
  MergeHiCursorInvariant mergeHiNbZeroHedgeStrictControlState 2 mergeHiNbZeroHedgeStrictControlCursor := by
-- proof
  refine
    { baseNonnegative := by decide
      ssaEquation := by decide
      ssbEquation := by decide
      destEquation := by decide
      mainRange := by decide
      leftWordBound := by decide
      rightWordBound := by decide
      tempCapacity := by decide
      tempValuesMode := ?_
      tempInvariant := by
        have hcapacity : 4 ≤ MERGESTATE_TEMP_SIZE := by decide
        simpa [mergeHiNbZeroHedgeStrictControlCursor,
          mergeHiNbZeroHedgeStrictControlState,
          mergeHiNbZeroHedgeRegressionCursor,
          mergeHiNbZeroHedgeRegressionState, TempStorageInv,
          TempStorage.multiplier] using hcapacity
      tempLive := by
        simp [mergeHiNbZeroHedgeStrictControlCursor,
          mergeHiNbZeroHedgeStrictControlState,
          mergeHiNbZeroHedgeRegressionCursor,
          mergeHiNbZeroHedgeRegressionState, TempStorage.Live]
      requestFits := by decide
      valuesMode := ?_
      stableFrame := ?_
      storageFrame := ?_ }
  · intro index hindex
    have hindex' : index < 2 := by
      simpa [mergeHiNbZeroHedgeStrictControlCursor,
        mergeHiNbZeroHedgeStrictControlState,
        mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeHiNbZeroHedgeStrictControlCursor,
        mergeHiNbZeroHedgeStrictControlState,
        mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · intro index hindex
    have hindex' : index < 3 := by
      simpa [mergeHiNbZeroHedgeStrictControlCursor,
        mergeHiNbZeroHedgeStrictControlState,
        mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeHiNbZeroHedgeStrictControlCursor,
        mergeHiNbZeroHedgeStrictControlState,
        mergeHiNbZeroHedgeRegressionCursor,
        mergeHiNbZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · simpa [mergeHiNbZeroHedgeStrictControlCursor] using
    MergeHiStableFrame.refl mergeHiNbZeroHedgeStrictControlState
  · simpa [mergeHiNbZeroHedgeStrictControlCursor] using
    MergeHiStorageFrame.refl mergeHiNbZeroHedgeStrictControlState

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[prepend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma MergeHiCorePost.prepend
  (origin : MergeState κ ν) (request : Nat)
  (current : TraceResult α)
  (next : α → TraceResult (MergeHiResult κ ν))
  (reference : α → Option (MergeHiResult κ ν))
  (value : α) (result : MergeHiResult κ ν)
  (hcurrent : current.result = some value)
  (hcurrentSafe : MovementTraceSafe current)
  (hnext : MergeHiCorePost origin request (next value)
    (reference value) result) :
  MergeHiCorePost origin request (current.bind next)
    (current.erase.bind reference) result := by
  exact
    { resultEq := by
      simp [TraceResult.bind, hcurrent, hnext.resultEq]
      returnCode := hnext.returnCode
      resultFuel := hnext.resultFuel
      traceSafe := MovementTraceSafe.bind current next value hcurrent
        hcurrentSafe hnext.traceSafe
      exactErasure := by
        have herase : current.erase = some value := hcurrent
        rw [TraceResult.erase_bind, herase]
        simpa using hnext.exactErasure
      tempInvariant := hnext.tempInvariant
      tempLive := hnext.tempLive
      requestFits := hnext.requestFits
      valuesMode := hnext.valuesMode
      stableFrame := hnext.stableFrame
      storageFrame := hnext.storageFrame }

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[reference_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma MergeHiCorePost.reference_eq
  {origin : MergeState κ ν} {request : Nat}
  {execution : TraceResult (MergeHiResult κ ν)}
  {first second : Option (MergeHiResult κ ν)}
  {result : MergeHiResult κ ν}
  (h : MergeHiCorePost origin request execution first result)
  (heq : first = second) :
  MergeHiCorePost origin request execution second result := by
  subst second
  exact h

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[movementTraceSafe_of_gallopTraceSafe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma movementTraceSafe_of_gallopTraceSafe
  (execution : TraceResult α) (h : GallopTraceSafe execution) :
  MovementTraceSafe execution :=
⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiTempReadTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiTempReadTraced_safe (storage : TempStorage κ ν)
  (index : Int) (hindex : TempIndexInBounds storage index)
  (hlive : storage.Live) :
  MovementTraceSafe (TraceResult.tempPayloadRead? storage index) := by
  constructor
  · simp [TraceResult.trace_tempPayloadRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_tempPayloadRead, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_tempPayloadRead]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, TempIndexInBounds] using hindex
  · rw [TraceResult.trace_tempPayloadRead]
    simpa [AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive, TempStorage.Live] using hlive

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMainKeyReadTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiMainKeyReadTraced_safe (slice : SortSlice κ ν)
  (index : Int) (hindex : SortSlice.IndexInBounds slice index) :
  MovementTraceSafe (TraceResult.sortSliceKeysRead? slice index) := by
  constructor
  · simp [TraceResult.trace_sortSliceKeysRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceKeysRead, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_sortSliceKeysRead]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, SortSlice.IndexInBounds] using hindex
  · simp [TraceResult.trace_sortSliceKeysRead,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mainDataCopyDecr_temp_eq_of_result](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mainDataCopyDecr_temp_eq_of_result
  (state : MergeState κ ν) (dst src : Int)
  (result : MergeHiDataCursorResult κ ν)
  (hresult : (mergeHiCopyDataDecrTraced? state dst src).result =
    some result) :
  result.state.a = state.a := by
  unfold mergeHiCopyDataDecrTraced? mainDataCopyDecrTraced? at hresult
  cases hcopy :
    (SortSlice.copyDecrTraced? state.a.hasValues state.data dst src).result with
  | none => simp [TraceResult.map, hcopy] at hresult
  | some copied =>
    simp [TraceResult.map, hcopy] at hresult
    subst result
    rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiCopyDataDecrTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma mergeHiCopyDataDecrTraced_safe
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {request : Nat}
  {cursor : MergeHiCursor κ ν}
-- given
  (hinvariant : MergeHiCursorInvariant origin request cursor)
  (hna : 0 < cursor.na) :
-- imply
  ∃ copied, (mergeHiCopyDataDecrTraced? cursor.state cursor.dest cursor.ssa).result = some copied ∧ MovementTraceSafe (mergeHiCopyDataDecrTraced? cursor.state cursor.dest cursor.ssa) ∧ MergeHiCursorInvariant origin request { cursor with state := copied.state dest := copied.dst ssa := copied.src na := cursor.na - 1 } ∧ copied.dst = cursor.dest - 1 ∧ copied.src = cursor.ssa - 1 := by
-- proof
  have hdest := hinvariant.destInBounds (by omega)
  have hsrc := hinvariant.ssaInBounds hna
  rcases mainDataCopyDecrTraced_safe cursor.state cursor.dest cursor.ssa
    hinvariant.tempInvariant hinvariant.tempLive hinvariant.valuesMode
    hdest hsrc with ⟨copied, hpost⟩
  have htemp := mainDataCopyDecr_temp_eq_of_result cursor.state cursor.dest
    cursor.ssa copied hpost.success
  have hnextInv : MergeHiCursorInvariant origin request
    { cursor with
      state := copied.state
      dest := copied.dst
      ssa := copied.src
      na := cursor.na - 1 } := by
    simpa only [hpost.dstDecrement, hpost.srcDecrement] using
      hinvariant.copyA copied.state hpost.frame htemp hpost.valuesMode hna
  exact ⟨copied, hpost.success, hpost.traceSafe, hnextInv,
    hpost.dstDecrement, hpost.srcDecrement⟩

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiCopyTempDecrTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma mergeHiCopyTempDecrTraced_safe
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {request : Nat}
  {cursor : MergeHiCursor κ ν}
-- given
  (hinvariant : MergeHiCursorInvariant origin request cursor)
  (hnb : 0 < cursor.nb) :
-- imply
  ∃ copied, (mergeHiCopyTempDecrTraced? cursor.state cursor.dest cursor.ssb).result = some copied ∧ MovementTraceSafe (mergeHiCopyTempDecrTraced? cursor.state cursor.dest cursor.ssb) ∧ MergeHiCursorInvariant origin request { cursor with state := copied.state dest := copied.dst ssb := copied.src nb := cursor.nb - 1 } ∧ copied.dst = cursor.dest - 1 ∧ copied.src = cursor.ssb - 1 := by
-- proof
  have hdest := hinvariant.destInBounds (by omega)
  have htemp := hinvariant.ssbInBounds hnb
  have hreadable := hinvariant.tempReadable hnb
  rcases tempToMainCellTraced_safe cursor.state cursor.dest cursor.ssb
    hdest htemp hinvariant.tempLive hreadable with
    ⟨state, hstate, htraceSafe, hframe⟩
  have hcore : tempToMainCell? cursor.state cursor.dest cursor.ssb =
    some state := by
    rwa [← erase_tempToMainCellTraced]
  have htempEq := tempToMainCell_temp_eq_of_eq_some cursor.state state
    cursor.dest cursor.ssb hcore
  have hentryMode : ∀ entry,
    mergeTempRead? cursor.state.a cursor.ssb = some entry →
      SortSlice.EntryMatchesValuesMode cursor.state.a.hasValues entry := by
    intro entry hentry
    have hindex : cursor.ssb = Int.ofNat (cursor.nb - 1) := by
      have heq := hinvariant.ssbEquation
      simp only [Int.ofNat_eq_natCast] at heq ⊢
      omega
    rcases hinvariant.tempValuesMode (cursor.nb - 1) (by omega) with
      ⟨stored, hstored, hstoredMode⟩
    rw [erase_mergeTempRead] at hstored
    simp only [zero_add] at hstored
    rw [hindex] at hentry
    have heq : stored = entry := Option.some.inj (hstored.symm.trans hentry)
    simpa [heq] using hstoredMode
  have hmode := tempToMainCell_valuesMode_of_eq_some cursor.state state
    cursor.dest cursor.ssb hinvariant.valuesMode hentryMode hcore
  let copied : MergeHiDataCursorResult κ ν :=
    { state := state, dst := cursor.dest - 1, src := cursor.ssb - 1 }
  have hcopied :
    (mergeHiCopyTempDecrTraced? cursor.state cursor.dest
      cursor.ssb).result = some copied := by
    simp [mergeHiCopyTempDecrTraced?, TraceResult.map, hstate, copied]
  have hnextInv : MergeHiCursorInvariant origin request
    { cursor with
      state := copied.state
      dest := copied.dst
      ssb := copied.src
      nb := cursor.nb - 1 } := by
    exact hinvariant.copyB state hframe htempEq hmode hnb
  exact ⟨copied, hcopied, MovementTraceSafe.map _ _ htraceSafe,
    hnextInv, rfl, rfl⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiSucceedTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
The `nb = 0` hedge is retained as an access-free success; the nonempty branch
consumes the classified final-copy provenance permit. -/
private lemma mergeHiSucceedTraced_safe
  (origin : MergeState κ ν) (request : Nat) (cursor : MergeHiCursor κ ν)
  (hinvariant : MergeHiCursorInvariant origin request cursor) :
  ∃ result, MergeHiCorePost origin request
    (mergeHiSucceedTraced? cursor) (mergeHiSucceed? cursor) result := by
  by_cases hnb : cursor.nb = 0
  · let result : MergeHiResult κ ν :=
    { state := cursor.state, returnCode := 0, fuelExhausted := false }
    refine ⟨result, ?_⟩
    refine
      { resultEq := ?_
        returnCode := rfl
        resultFuel := rfl
        traceSafe := ?_
        exactErasure := erase_mergeHiSucceedTraced cursor
        tempInvariant := hinvariant.tempInvariant
        tempLive := hinvariant.tempLive
        requestFits := hinvariant.requestFits
        valuesMode := hinvariant.valuesMode
        stableFrame := hinvariant.stableFrame
        storageFrame := hinvariant.storageFrame }
    · simp [mergeHiSucceedTraced?, hnb, TraceResult.map,
      TraceResult.pure, result]
    · rw [mergeHiSucceedTraced?, if_pos hnb]
      exact MovementTraceSafe.map _ _
        (MovementTraceSafe.pure cursor.state)
  · have hnbPositive : 0 < cursor.nb := Nat.pos_of_ne_zero hnb
    have hstart :
      cursor.dest - Int.ofNat (cursor.nb - 1) =
        cursor.basea + Int.ofNat cursor.na := by
      have hdest := hinvariant.destEquation
      simp only [Int.ofNat_eq_natCast, Nat.cast_add] at hdest ⊢
      omega
    have hmain : SortSlice.RangeInBounds cursor.state.data
      (cursor.dest - Int.ofNat (cursor.nb - 1)) cursor.nb := by
      rw [hstart]
      constructor
      · exact add_nonneg hinvariant.baseNonnegative (Int.natCast_nonneg _)
      · have hrange := hinvariant.mainRange
        simpa only [Int.ofNat_eq_natCast, Nat.cast_add, add_assoc] using hrange
    have htemp : TempRangeInBounds cursor.state.a 0 cursor.nb := by
      constructor
      · rfl
      · simpa [Int.ofNat_eq_natCast] using
        Int.ofNat_le.mpr hinvariant.tempCapacity
    rcases tempToMainMemcpyTraced_post (.hi .finalTempToData)
      mergeHiFinalTempToDataPermit cursor.nb cursor.state
      (cursor.dest - Int.ofNat (cursor.nb - 1)) 0 hmain htemp
      hinvariant.tempValuesMode hinvariant.tempInvariant hinvariant.tempLive
      hinvariant.valuesMode with ⟨state, hpost⟩
    let result : MergeHiResult κ ν :=
      { state := state, returnCode := 0, fuelExhausted := false }
    refine ⟨result, ?_⟩
    refine
      { resultEq := ?_
        returnCode := rfl
        resultFuel := rfl
        traceSafe := ?_
        exactErasure := erase_mergeHiSucceedTraced cursor
        tempInvariant := hpost.tempInvariant
        tempLive := hpost.tempLive
        requestFits := ?_
        valuesMode := hpost.valuesMode
        stableFrame := hinvariant.stableFrame.trans
          (MergeHiStableFrame.of_movement hpost.frame)
        storageFrame := hinvariant.storageFrame.trans
          (MergeHiStorageFrame.of_movement hpost.frame) }
    · rw [mergeHiSucceedTraced?, if_neg hnb]
      change Option.map _ _ = some result
      rw [hpost.success]
      rfl
    · rw [mergeHiSucceedTraced?, if_neg hnb]
      exact MovementTraceSafe.map _ _ hpost.traceSafe
    · change request ≤ state.alloced.toNat
      rwa [hpost.frame.alloced]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mainDataMemmove_temp_eq_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mainDataMemmove_temp_eq_of_eq_some
  (state result : MergeState κ ν) (dst src : Int) (count : Nat)
  (hresult : mainDataMemmove? state dst src count = some result) :
  result.a = state.a := by
  unfold mainDataMemmove? at hresult
  obtain ⟨data, _hmove, hfinal⟩ := Option.bind_eq_some_iff.mp hresult
  injection hfinal with hfinal
  subst result
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiMoveABlockTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma mergeHiMoveABlockTraced_safe
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {request : Nat}
  {cursor : MergeHiCursor κ ν}
  {count : Nat}
-- given
  (hinvariant : MergeHiCursorInvariant origin request cursor)
  (hcount : count ≤ cursor.na) :
-- imply
  ∃ moved, (mergeHiMoveABlockTraced? cursor count).result = some moved ∧ MovementTraceSafe (mergeHiMoveABlockTraced? cursor count) ∧ MergeHiCursorInvariant origin request moved ∧ moved.na = cursor.na - count ∧ moved.nb = cursor.nb := by
-- proof
  by_cases hzero : count = 0
  · subst count
    refine ⟨cursor, ?_, ?_, hinvariant, rfl, rfl⟩
    · rfl
    · exact MovementTraceSafe.pure cursor
  · have hpositive : 0 < count := Nat.pos_of_ne_zero hzero
    have hsrcStart : cursor.ssa - Int.ofNat count + 1 =
      cursor.basea + Int.ofNat (cursor.na - count) := by
      have heq := hinvariant.ssaEquation
      simp only [Int.ofNat_eq_natCast, Nat.cast_sub hcount] at heq ⊢
      omega
    have hdstStart : cursor.dest - Int.ofNat count + 1 =
      cursor.basea + Int.ofNat (cursor.na + cursor.nb - count) := by
      have heq := hinvariant.destEquation
      have hsum : count ≤ cursor.na + cursor.nb := hcount.trans (Nat.le_add_right _ _)
      simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hsum]
        at heq ⊢
      omega
    have hsrc : SortSlice.RangeInBounds cursor.state.data
      (cursor.ssa - Int.ofNat count + 1) count := by
      rw [hsrcStart]
      constructor
      · exact add_nonneg hinvariant.baseNonnegative (Int.natCast_nonneg _)
      · have hrange := hinvariant.mainRange
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hcount]
          at hrange ⊢
        omega
    have hdst : SortSlice.RangeInBounds cursor.state.data
      (cursor.dest - Int.ofNat count + 1) count := by
      rw [hdstStart]
      constructor
      · exact add_nonneg hinvariant.baseNonnegative (Int.natCast_nonneg _)
      · have hrange := hinvariant.mainRange
        have hsum : count ≤ cursor.na + cursor.nb :=
          hcount.trans (Nat.le_add_right _ _)
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hsum]
          at hrange ⊢
        omega
    rcases mainDataMemmoveTraced_safe cursor.state
      (cursor.dest - Int.ofNat count + 1)
      (cursor.ssa - Int.ofNat count + 1) count
      hinvariant.tempInvariant hinvariant.tempLive hinvariant.valuesMode
      hdst hsrc with ⟨state, hpost⟩
    have htemp := mainDataMemmove_temp_eq_of_eq_some cursor.state state
      (cursor.dest - Int.ofNat count + 1)
      (cursor.ssa - Int.ofNat count + 1) count (by
        rw [← hpost.exactErasure]
        exact hpost.success)
    let moved : MergeHiCursor κ ν :=
      { cursor with
        state := state
        dest := cursor.dest - Int.ofNat count
        ssa := cursor.ssa - Int.ofNat count
        na := cursor.na - count }
    have hmovedInv : MergeHiCursorInvariant origin request moved := by
      exact hinvariant.copyABlock count hcount state hpost.frame htemp
        hpost.valuesMode
    refine ⟨moved, ?_, ?_, hmovedInv, rfl, rfl⟩
    · rw [mergeHiMoveABlockTraced?, if_neg hzero]
      simp only [TraceResult.map]
      rw [hpost.success]
      rfl
    · rw [mergeHiMoveABlockTraced?, if_neg hzero]
      exact MovementTraceSafe.map _ _ hpost.traceSafe

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiMoveBBlockTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma mergeHiMoveBBlockTraced_safe
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {request : Nat}
  {cursor : MergeHiCursor κ ν}
  {count : Nat}
-- given
  (hinvariant : MergeHiCursorInvariant origin request cursor)
  (hcount : count ≤ cursor.nb) :
-- imply
  ∃ moved, (mergeHiMoveBBlockTraced? cursor count).result = some moved ∧ MovementTraceSafe (mergeHiMoveBBlockTraced? cursor count) ∧ MergeHiCursorInvariant origin request moved ∧ moved.na = cursor.na ∧ moved.nb = cursor.nb - count := by
-- proof
  by_cases hzero : count = 0
  · subst count
    refine ⟨cursor, ?_, ?_, hinvariant, rfl, rfl⟩
    · rfl
    · exact MovementTraceSafe.pure cursor
  · have hsrcStart : cursor.ssb - Int.ofNat count + 1 =
    Int.ofNat (cursor.nb - count) := by
    have heq := hinvariant.ssbEquation
    simp only [Int.ofNat_eq_natCast, Nat.cast_sub hcount] at heq ⊢
    omega
    have hdstStart : cursor.dest - Int.ofNat count + 1 =
      cursor.basea + Int.ofNat (cursor.na + cursor.nb - count) := by
      have heq := hinvariant.destEquation
      have hsum : count ≤ cursor.na + cursor.nb :=
        hcount.trans (Nat.le_add_left _ _)
      simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hsum]
        at heq ⊢
      omega
    have hmain : SortSlice.RangeInBounds cursor.state.data
      (cursor.dest - Int.ofNat count + 1) count := by
      rw [hdstStart]
      constructor
      · exact add_nonneg hinvariant.baseNonnegative (Int.natCast_nonneg _)
      · have hrange := hinvariant.mainRange
        have hsum : count ≤ cursor.na + cursor.nb :=
          hcount.trans (Nat.le_add_left _ _)
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hsum]
          at hrange ⊢
        omega
    have htemp : TempRangeInBounds cursor.state.a
      (cursor.ssb - Int.ofNat count + 1) count := by
      rw [hsrcStart]
      constructor
      · exact Int.natCast_nonneg _
      · have hcapacity := hinvariant.tempCapacity
        have hbound : cursor.nb - count + count ≤
          cursor.state.a.cells.size := by
          rwa [Nat.sub_add_cancel hcount]
        simpa only [Int.ofNat_eq_natCast, Nat.cast_add,
          Nat.cast_sub hcount] using Int.ofNat_le.mpr hbound
    have htempMode : TempRangeValuesMode cursor.state.a
      (cursor.ssb - Int.ofNat count + 1) count := by
      rw [hsrcStart]
      intro offset hoffset
      have htotal : cursor.nb - count + offset < cursor.nb := by omega
      rcases hinvariant.tempValuesMode (cursor.nb - count + offset) htotal with
        ⟨entry, hread, hmode⟩
      refine ⟨entry, ?_, hmode⟩
      simpa only [zero_add, Int.ofNat_eq_natCast, Nat.cast_add] using hread
    rcases tempToMainMemcpyTraced_post (.hi .gallopTempToData)
      mergeHiGallopTempToDataPermit count cursor.state
      (cursor.dest - Int.ofNat count + 1)
      (cursor.ssb - Int.ofNat count + 1) hmain htemp htempMode
      hinvariant.tempInvariant hinvariant.tempLive hinvariant.valuesMode with
      ⟨state, hpost⟩
    have hcore : tempToMainMemcpy? count cursor.state
      (cursor.dest - Int.ofNat count + 1)
      (cursor.ssb - Int.ofNat count + 1) = some state := by
      rwa [← hpost.exactErasure]
    have htempEq := tempToMainMemcpy_temp_eq_of_eq_some count cursor.state state
      (cursor.dest - Int.ofNat count + 1)
      (cursor.ssb - Int.ofNat count + 1) hcore
    let moved : MergeHiCursor κ ν :=
      { cursor with
        state := state
        dest := cursor.dest - Int.ofNat count
        ssb := cursor.ssb - Int.ofNat count
        nb := cursor.nb - count }
    have hmovedInv : MergeHiCursorInvariant origin request moved := by
      exact hinvariant.copyBBlock count hcount state hpost.frame htempEq
        hpost.valuesMode
    refine ⟨moved, ?_, ?_, hmovedInv, rfl, rfl⟩
    · rw [mergeHiMoveBBlockTraced?, if_neg hzero]
      simp only [TraceResult.map]
      rw [hpost.success]
      rfl
    · rw [mergeHiMoveBBlockTraced?, if_neg hzero]
      exact MovementTraceSafe.map _ _ hpost.traceSafe

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiGallopBFinishTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiGallopBFinishTraced_safe
  (origin : MergeState κ ν) (request fuel : Nat)
  (afterB : MergeHiCursor κ ν) (aCount bCount : Nat)
  (movedB : MergeHiCursor κ ν)
  (hinvariant : MergeHiCursorInvariant origin request movedB)
  (hfuel : MergeHiFuelInvariant fuel movedB)
  (hna : 0 < movedB.na)
  (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
  (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
  (hnext : MergeHiContinuationSafe origin request fuel nextTraced next) :
  ∃ result, MergeHiCorePost origin request
    (mergeHiGallopBFinishTraced? afterB aCount bCount movedB nextTraced)
    (mergeHiGallopBFinish? afterB aCount bCount movedB next) result := by
  by_cases hterminal : movedB.nb = 0 ∨ movedB.nb = 1
  · rcases hnext movedB hinvariant hfuel with ⟨result, hresult⟩
    exact ⟨result, by
      simpa [mergeHiGallopBFinishTraced?, mergeHiGallopBFinish?, hterminal]
        using hresult⟩
  · rcases mergeHiCopyDataDecrTraced_safe origin request movedB hinvariant
    hna with ⟨copiedA, hcopy, hcopySafe, hcopiedInv, _hdst, _hsrc⟩
    let afterA : MergeHiCursor κ ν :=
      { movedB with
        state := copiedA.state
        dest := copiedA.dst
        ssa := copiedA.src
        na := movedB.na - 1 }
    have hafterInv : MergeHiCursorInvariant origin request afterA := hcopiedInv
    have hafterFuel : MergeHiFuelInvariant fuel afterA := by
      have hf := hfuel
      change movedB.na + movedB.nb < fuel at hf
      change movedB.na - 1 + movedB.nb < fuel
      omega
    let tracedTail := fun copied : MergeHiDataCursorResult κ ν =>
      let cursor : MergeHiCursor κ ν :=
        { movedB with
          state := copied.state
          dest := copied.dst
          ssa := copied.src
          na := movedB.na - 1 }
      if cursor.na = 0 then
        nextTraced cursor
      else if mergeHiCountAtLeast aCount MIN_GALLOP ||
        mergeHiCountAtLeast bCount MIN_GALLOP then
        nextTraced { cursor with phase := .galloping aCount bCount }
      else
        let minGallop := afterB.minGallop + 1
        let state := { cursor.state with min_gallop := minGallop }
        nextTraced
          { cursor with
            state := state
            minGallop := minGallop
            phase := .straight 0 0 }
    let tail := fun copied : MergeHiDataCursorResult κ ν =>
      let cursor : MergeHiCursor κ ν :=
        { movedB with
          state := copied.state
          dest := copied.dst
          ssa := copied.src
          na := movedB.na - 1 }
      if cursor.na = 0 then
        next cursor
      else if mergeHiCountAtLeast aCount MIN_GALLOP ||
        mergeHiCountAtLeast bCount MIN_GALLOP then
        next { cursor with phase := .galloping aCount bCount }
      else
        let minGallop := afterB.minGallop + 1
        let state := { cursor.state with min_gallop := minGallop }
        next
          { cursor with
            state := state
            minGallop := minGallop
            phase := .straight 0 0 }
    have htail : ∃ result, MergeHiCorePost origin request
      (tracedTail copiedA) (tail copiedA) result := by
      by_cases hzero : afterA.na = 0
      · rcases hnext afterA hafterInv hafterFuel with ⟨result, hresult⟩
        have hzero' : movedB.na - 1 = 0 := by simpa [afterA] using hzero
        exact ⟨result, by
          simp only [tracedTail, tail]
          rw [if_pos hzero', if_pos hzero']
          exact hresult⟩
      · have hzero' : ¬ movedB.na - 1 = 0 := by simpa [afterA] using hzero
        let gallopAgain := mergeHiCountAtLeast aCount MIN_GALLOP ||
          mergeHiCountAtLeast bCount MIN_GALLOP
        by_cases hgallop : gallopAgain = true
        · let nextCursor : MergeHiCursor κ ν :=
          { afterA with phase := .galloping aCount bCount }
          have hnextInv : MergeHiCursorInvariant origin request nextCursor := by
            exact hafterInv.setControl afterA.minGallop
              (.galloping aCount bCount)
          have hnextFuel : MergeHiFuelInvariant fuel nextCursor := by
            change afterA.na + afterA.nb < fuel
            exact hafterFuel
          obtain ⟨result, hresult⟩ := hnext nextCursor hnextInv hnextFuel
          exact ⟨result, by
            simp only [tracedTail, tail]
            rw [if_neg hzero', if_neg hzero']
            have hgallop' :
              (mergeHiCountAtLeast aCount MIN_GALLOP ||
                mergeHiCountAtLeast bCount MIN_GALLOP) = true := by
              exact hgallop
            rw [if_pos hgallop', if_pos hgallop']
            exact hresult⟩
        · let minGallop := afterB.minGallop + 1
          let nextCursor : MergeHiCursor κ ν :=
            { afterA with
              state := { afterA.state with min_gallop := minGallop }
              minGallop := minGallop
              phase := .straight 0 0 }
          have hnextInv : MergeHiCursorInvariant origin request nextCursor := by
            exact (hafterInv.setMinGallop minGallop).setControl minGallop
              (.straight 0 0)
          have hnextFuel : MergeHiFuelInvariant fuel nextCursor := by
            change afterA.na + afterA.nb < fuel
            exact hafterFuel
          obtain ⟨result, hresult⟩ := hnext nextCursor hnextInv hnextFuel
          exact ⟨result, by
            simp only [tracedTail, tail]
            rw [if_neg hzero', if_neg hzero']
            have hgallop' : ¬
              (mergeHiCountAtLeast aCount MIN_GALLOP ||
                mergeHiCountAtLeast bCount MIN_GALLOP) = true := by
              exact hgallop
            rw [if_neg hgallop', if_neg hgallop']
            exact hresult⟩
    obtain ⟨result, htail⟩ := htail
    have hpost := MergeHiCorePost.prepend origin request
      (mergeHiCopyDataDecrTraced? movedB.state movedB.dest movedB.ssa)
      tracedTail tail copiedA result hcopy hcopySafe htail
    exact ⟨result, by
      simpa [mergeHiGallopBFinishTraced?, mergeHiGallopBFinish?, hterminal,
        tracedTail, tail] using hpost⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiGallopBAfterTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiGallopBAfterTraced_safe
  (origin : MergeState κ ν) (request fuel : Nat)
  (afterB : MergeHiCursor κ ν) (aCount : Nat)
  (gallopB : GallopResult)
  (hinvariant : MergeHiCursorInvariant origin request afterB)
  (hfuel : MergeHiFuelInvariant fuel afterB)
  (hna : 0 < afterB.na)
  (_hbound : gallopB.index ≤ afterB.nb)
  (hnotFuel : gallopB.fuelExhausted = false)
  (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
  (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
  (hnext : MergeHiContinuationSafe origin request fuel nextTraced next) :
  ∃ result, MergeHiCorePost origin request
    (mergeHiGallopBAfterTraced? afterB aCount gallopB nextTraced)
    (mergeHiGallopBAfter? afterB aCount gallopB next) result := by
  let bCount := afterB.nb - gallopB.index
  have hbCount : bCount ≤ afterB.nb := Nat.sub_le _ _
  rcases mergeHiMoveBBlockTraced_safe origin request afterB hinvariant
    bCount hbCount with
    ⟨movedB, hmove, hmoveSafe, hmovedInv, hmovedNa, hmovedNb⟩
  have hmovedFuel : MergeHiFuelInvariant fuel movedB := by
    have hf := hfuel
    change afterB.na + afterB.nb < fuel at hf
    change movedB.na + movedB.nb < fuel
    rw [hmovedNa, hmovedNb]
    omega
  have hmovedNaPositive : 0 < movedB.na := by simpa [hmovedNa] using hna
  rcases mergeHiGallopBFinishTraced_safe origin request fuel afterB aCount
    bCount movedB hmovedInv hmovedFuel hmovedNaPositive nextTraced next hnext with
    ⟨result, hfinish⟩
  have hpost := MergeHiCorePost.prepend origin request
    (mergeHiMoveBBlockTraced? afterB bCount)
    (fun moved => mergeHiGallopBFinishTraced? afterB aCount bCount moved
      nextTraced)
    (fun moved => mergeHiGallopBFinish? afterB aCount bCount moved next)
    movedB result hmove hmoveSafe hfinish
  exact ⟨result, by
    simpa [mergeHiGallopBAfterTraced?, mergeHiGallopBAfter?, hnotFuel,
      bCount] using hpost⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiCopyATraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
where CPython jumps to it.  Its right-shift is overlap-safe memmove, followed
by the one physical temporary read that installs the smallest right entry. -/
private lemma mergeHiCopyATraced_safe
  (origin : MergeState κ ν) (request : Nat) (cursor : MergeHiCursor κ ν)
  (hinvariant : MergeHiCursorInvariant origin request cursor)
  (htail : cursor.nb = 1 ∧ 0 < cursor.na) :
  ∃ result, MergeHiCorePost origin request
    (mergeHiCopyATraced? cursor) (mergeHiCopyA? cursor) result := by
  have hsrcEq : cursor.ssa + (1 - Int.ofNat cursor.na) = cursor.basea := by
    have heq := hinvariant.ssaEquation
    simp only [Int.ofNat_eq_natCast] at heq ⊢
    omega
  have hdstEq : cursor.dest + (1 - Int.ofNat cursor.na) =
    cursor.basea + 1 := by
    have heq := hinvariant.destEquation
    simp only [htail.1, Int.ofNat_eq_natCast, Nat.cast_add,
      Nat.cast_one] at heq ⊢
    omega
  have hsrcRange : SortSlice.RangeInBounds cursor.state.data
    (cursor.ssa + (1 - Int.ofNat cursor.na)) cursor.na := by
    rw [hsrcEq]
    constructor
    · exact hinvariant.baseNonnegative
    · have hrange := hinvariant.mainRange
      simp only [htail.1, Int.ofNat_eq_natCast, Nat.cast_add,
        Nat.cast_one] at hrange ⊢
      omega
  have hdstRange : SortSlice.RangeInBounds cursor.state.data
    (cursor.dest + (1 - Int.ofNat cursor.na)) cursor.na := by
    rw [hdstEq]
    constructor
    · exact add_nonneg hinvariant.baseNonnegative (by norm_num)
    · have hrange := hinvariant.mainRange
      simp only [htail.1, Int.ofNat_eq_natCast, Nat.cast_add,
        Nat.cast_one] at hrange ⊢
      omega
  rcases mainDataMemmoveTraced_safe cursor.state
    (cursor.dest + (1 - Int.ofNat cursor.na))
    (cursor.ssa + (1 - Int.ofNat cursor.na)) cursor.na
    hinvariant.tempInvariant hinvariant.tempLive hinvariant.valuesMode
    hdstRange hsrcRange with ⟨shifted, hshift⟩
  have hshiftCore : mainDataMemmove? cursor.state
    (cursor.dest + (1 - Int.ofNat cursor.na))
    (cursor.ssa + (1 - Int.ofNat cursor.na)) cursor.na = some shifted := by
    rwa [← hshift.exactErasure]
  have htempEq : shifted.a = cursor.state.a :=
    mainDataMemmove_temp_eq_of_eq_some cursor.state shifted _ _ _ hshiftCore
  have hcellDstEq : cursor.dest - Int.ofNat cursor.na = cursor.basea := by
    have heq := hinvariant.destEquation
    simp only [htail.1, Int.ofNat_eq_natCast, Nat.cast_add,
      Nat.cast_one] at heq ⊢
    omega
  have hcellMain : SortSlice.IndexInBounds shifted.data
    (cursor.dest - Int.ofNat cursor.na) := by
    rw [hcellDstEq]
    constructor
    · exact hinvariant.baseNonnegative
    · have hrange := hinvariant.mainRange
      have hsize := hshift.frame.dataSize
      simp only [htail.1, Int.ofNat_eq_natCast, Nat.cast_add,
        Nat.cast_one] at hrange
      rw [hsize]
      simp only [Int.ofNat_eq_natCast]
      omega
  have hssb : cursor.ssb = 0 := by
    have heq := hinvariant.ssbEquation
    simp only [htail.1, Int.ofNat_eq_natCast, Nat.cast_one] at heq
    omega
  have hcellTemp : TempIndexInBounds shifted.a cursor.ssb := by
    rw [hssb, htempEq]
    constructor
    · rfl
    · have hcapacity := hinvariant.tempCapacity
      simp only [htail.1] at hcapacity
      have hpositive : 0 < cursor.state.a.cells.size := by omega
      rw [Int.ofNat_eq_natCast]
      exact_mod_cast hpositive
  have hshiftedTempMode : TempRangeValuesMode shifted.a 0 1 := by
    simpa only [htempEq, htail.1] using hinvariant.tempValuesMode
  obtain ⟨entry, hentryRead, hentryMode⟩ := hshiftedTempMode.head
  have hreadable : ∃ entry, mergeTempRead? shifted.a cursor.ssb = some entry := by
    refine ⟨entry, ?_⟩
    rwa [hssb]
  rcases tempToMainCellTraced_safe shifted
    (cursor.dest - Int.ofNat cursor.na) cursor.ssb hcellMain hcellTemp
    hshift.tempLive hreadable with ⟨state, hcell, hcellSafe, hcellFrame⟩
  have hcellCore : tempToMainCell? shifted
    (cursor.dest - Int.ofNat cursor.na) cursor.ssb = some state := by
    rwa [← erase_tempToMainCellTraced]
  have hstateMode :
    SortSlice.ValuesModeInvariant state.a.hasValues state.data := by
    apply tempToMainCell_valuesMode_of_eq_some shifted state
      (cursor.dest - Int.ofNat cursor.na) cursor.ssb hshift.valuesMode
      _ hcellCore
    intro other hother
    rw [hssb] at hother
    rw [hentryRead] at hother
    injection hother with hother
    subst other
    exact hentryMode
  let result : MergeHiResult κ ν :=
    { state := state, returnCode := 0, fuelExhausted := false }
  refine ⟨result, ?_⟩
  refine
    { resultEq := ?_
      returnCode := rfl
      resultFuel := rfl
      traceSafe := ?_
      exactErasure := erase_mergeHiCopyATraced cursor
      tempInvariant := hcellFrame.tempStorageInv hshift.tempInvariant
      tempLive := hcellFrame.live hshift.tempLive
      requestFits := ?_
      valuesMode := hstateMode
      stableFrame := (hinvariant.stableFrame.trans
        (MergeHiStableFrame.of_movement hshift.frame)).trans
          (MergeHiStableFrame.of_movement hcellFrame)
      storageFrame := (hinvariant.storageFrame.trans
        (MergeHiStorageFrame.of_movement hshift.frame)).trans
          (MergeHiStorageFrame.of_movement hcellFrame) }
  · rw [mergeHiCopyATraced?, if_pos htail]
    dsimp only
    unfold TraceResult.bind
    rw [hshift.success]
    change Option.map _
      (tempToMainCellTraced? shifted
        (cursor.dest - Int.ofNat cursor.na) cursor.ssb).result = some result
    rw [hcell]
    rfl
  · rw [mergeHiCopyATraced?, if_pos htail]
    apply MovementTraceSafe.bind _ _ shifted hshift.success hshift.traceSafe
    exact MovementTraceSafe.map _ _ hcellSafe
  · change request ≤ state.alloced.toNat
    rwa [hcellFrame.alloced, hshift.frame.alloced]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiHasAccess_bind_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiHasAccess_bind_left
  (current : TraceResult α) (next : α → TraceResult β)
  (kind : AccessKind) (region : AccessRegion)
  (hcurrent : current.trace.HasAccess kind region) :
  (current.bind next).trace.HasAccess kind region := by
  rw [TraceResult.trace_bind]
  cases current.result with
  | none => exact hcurrent
  | some value => exact hcurrent.compose_left

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiHasAccess_bind_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiHasAccess_bind_right
  (current : TraceResult α) (next : α → TraceResult β)
  (value : α) (kind : AccessKind) (region : AccessRegion)
  (hresult : current.result = some value)
  (hnext : (next value).trace.HasAccess kind region) :
  (current.bind next).trace.HasAccess kind region := by
  rwa [TraceResult.trace_bind, hresult]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiHasTempAccess_bind_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiHasTempAccess_bind_left
  (current : TraceResult α) (next : α → TraceResult β)
  (kind : AccessKind) (hcurrent : current.trace.HasTempAccess kind) :
  (current.bind next).trace.HasTempAccess kind := by
  obtain ⟨backing, hcurrent⟩ := hcurrent
  exact ⟨backing, mergeHiHasAccess_bind_left current next kind
    (.tempPayload backing) hcurrent⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiHasTempAccess_bind_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiHasTempAccess_bind_right
  (current : TraceResult α) (next : α → TraceResult β)
  (value : α) (kind : AccessKind)
  (hresult : current.result = some value)
  (hnext : (next value).trace.HasTempAccess kind) :
  (current.bind next).trace.HasTempAccess kind := by
  obtain ⟨backing, hnext⟩ := hnext
  exact ⟨backing, mergeHiHasAccess_bind_right current next value kind
    (.tempPayload backing) hresult hnext⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiTempPayloadRead_hasTempAccess](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiTempPayloadRead_hasTempAccess
  (storage : TempStorage κ ν) (index : Int) :
  (TraceResult.tempPayloadRead? storage index).trace.HasTempAccess .read := by
  refine ⟨storage.backing, ?_⟩
  refine ⟨AccessEvent.mk .read (.tempPayload storage.backing) index
    storage.cells.size, ?_, rfl, rfl⟩
  simp [TraceResult.trace_tempPayloadRead, AccessTrace.singletonAccess]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiTempToMainCell_hasTempRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiTempToMainCell_hasTempRead
  (state : MergeState κ ν) (mainDst tempSrc : Int) :
  (tempToMainCellTraced? state mainDst tempSrc).trace.HasTempAccess .read := by
  have hkey : (tempToMainKeyTraced? state mainDst tempSrc).trace.HasTempAccess
    .read := by
    unfold tempToMainKeyTraced?
    exact mergeHiHasTempAccess_bind_left _ _ .read
      (mergeHiTempPayloadRead_hasTempAccess state.a tempSrc)
  unfold tempToMainCellTraced?
  exact mergeHiHasTempAccess_bind_left _ _ .read hkey

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiSucceedTraced_hasTempRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiSucceedTraced_hasTempRead
  (origin : MergeState κ ν) (request : Nat)
  (cursor : MergeHiCursor κ ν)
  (hinvariant : MergeHiCursorInvariant origin request cursor)
  (hnb : 0 < cursor.nb) :
  (mergeHiSucceedTraced? cursor).trace.HasTempAccess .read := by
  have hstart : cursor.dest - Int.ofNat (cursor.nb - 1) =
    cursor.basea + Int.ofNat cursor.na := by
    have hdest := hinvariant.destEquation
    simp only [Int.ofNat_eq_natCast, Nat.cast_add] at hdest ⊢
    omega
  have hmain : SortSlice.RangeInBounds cursor.state.data
    (cursor.dest - Int.ofNat (cursor.nb - 1)) cursor.nb := by
    rw [hstart]
    constructor
    · exact add_nonneg hinvariant.baseNonnegative (Int.natCast_nonneg _)
    · have hrange := hinvariant.mainRange
      simpa only [Int.ofNat_eq_natCast, Nat.cast_add, add_assoc] using hrange
  have htemp : TempRangeInBounds cursor.state.a 0 cursor.nb := by
    constructor
    · rfl
    · simpa [Int.ofNat_eq_natCast] using
      Int.ofNat_le.mpr hinvariant.tempCapacity
  rcases tempToMainMemcpyTraced_post (.hi .finalTempToData)
    mergeHiFinalTempToDataPermit cursor.nb cursor.state
    (cursor.dest - Int.ofNat (cursor.nb - 1)) 0 hmain htemp
    hinvariant.tempValuesMode hinvariant.tempInvariant hinvariant.tempLive
    hinvariant.valuesMode with ⟨_, hpost⟩
  rw [mergeHiSucceedTraced?, if_neg (Nat.ne_of_gt hnb)]
  exact hpost.tempReadEvent hnb

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiCopyATraced_hasTempRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiCopyATraced_hasTempRead
  (origin : MergeState κ ν) (request : Nat)
  (cursor : MergeHiCursor κ ν)
  (hinvariant : MergeHiCursorInvariant origin request cursor)
  (htail : cursor.nb = 1 ∧ 0 < cursor.na) :
  (mergeHiCopyATraced? cursor).trace.HasTempAccess .read := by
  have hsrcEq : cursor.ssa + (1 - Int.ofNat cursor.na) = cursor.basea := by
    have heq := hinvariant.ssaEquation
    simp only [Int.ofNat_eq_natCast] at heq ⊢
    omega
  have hdstEq : cursor.dest + (1 - Int.ofNat cursor.na) =
    cursor.basea + 1 := by
    have heq := hinvariant.destEquation
    simp only [htail.1, Int.ofNat_eq_natCast, Nat.cast_add,
      Nat.cast_one] at heq ⊢
    omega
  have hsrc : SortSlice.RangeInBounds cursor.state.data
    (cursor.ssa + (1 - Int.ofNat cursor.na)) cursor.na := by
    rw [hsrcEq]
    constructor
    · exact hinvariant.baseNonnegative
    · have hrange := hinvariant.mainRange
      simp only [htail.1, Int.ofNat_eq_natCast, Nat.cast_add,
        Nat.cast_one] at hrange ⊢
      omega
  have hdst : SortSlice.RangeInBounds cursor.state.data
    (cursor.dest + (1 - Int.ofNat cursor.na)) cursor.na := by
    rw [hdstEq]
    constructor
    · exact add_nonneg hinvariant.baseNonnegative (by norm_num)
    · have hrange := hinvariant.mainRange
      simp only [htail.1, Int.ofNat_eq_natCast, Nat.cast_add,
        Nat.cast_one] at hrange ⊢
      omega
  rcases mainDataMemmoveTraced_safe cursor.state
    (cursor.dest + (1 - Int.ofNat cursor.na))
    (cursor.ssa + (1 - Int.ofNat cursor.na)) cursor.na
    hinvariant.tempInvariant hinvariant.tempLive hinvariant.valuesMode
    hdst hsrc with ⟨shifted, hshift⟩
  rw [mergeHiCopyATraced?, if_pos htail]
  exact mergeHiHasTempAccess_bind_right _ _ shifted .read hshift.success
    (mergeHiTempToMainCell_hasTempRead shifted
      (cursor.dest - Int.ofNat cursor.na) cursor.ssb)

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiInitialLoop_hasTempRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiInitialLoop_hasTempRead
  (fuel : Nat) (cursor : MergeHiCursor κ ν)
  (hna : 0 < cursor.na) (hnb : 1 < cursor.nb)
  (hphase : cursor.phase = .straight 0 0) :
  (mergeHiLoopTraced? (fuel + 1) cursor).trace.HasTempAccess .read := by
  have hterminal : ¬ (cursor.na = 0 ∨ cursor.nb = 0) := by omega
  have hone : ¬ cursor.nb = 1 := by omega
  rw [mergeHiLoopTraced?, if_neg hterminal, if_neg hone, hphase]
  exact mergeHiHasTempAccess_bind_left _ _ .read
    (mergeHiTempPayloadRead_hasTempAccess cursor.state.a cursor.ssb)

end CPythonListsort

namespace CPythonListsort

/--
[mergeHi_prepare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
lemma mergeHi_prepare
  {κ : Type u}
  {ν : Type v}
  {pre : MergeState κ ν}
  {scanned i : Nat}
  {call : MergeAtCall κ ν}
-- given
  (hlayout : PendingLayout pre scanned)
  (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
  (hprepare : prepareMergeAt? pre i = some (.mergeHi call))
  (hInv : TempStorageInv pre.a pre.alloced)
  (hLive : pre.a.Live)
  (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data) :
-- imply
  ∃ copied forced, MergeHiPrepared pre scanned i call copied forced := by
-- proof
  have hrequest := mergeGetmem_hi_request_bound pre scanned i call hlayout hmax
    hprepare
  have hgeometry := mergeHi_callsite_safety_geometry pre scanned i call hlayout
    hmax hprepare
  have hdispatch := (prepareMergeAt_hi_callsite_of_eq_some pre i call hprepare).2
  have hevidence := hgeometry.evidence
  have hcallInv : TempStorageInv call.state.a call.state.alloced := by
    simpa only [hevidence.storage_eq, hevidence.alloced_eq] using hInv
  have hcallLive : call.state.a.Live := by
    simpa only [hevidence.storage_eq] using hLive
  have hcallMode :
    SortSlice.ValuesModeInvariant call.state.a.hasValues call.state.data := by
    simpa only [hevidence.hasValues_eq, hevidence.data_eq] using hMode
  have hallocPost : MergeGetmemStoragePost call.state
    (BitVec.ofNat 64 call.nb) (mergeHiAllocated call) := by
    exact mergeGetmem_storage_valid call.state (BitVec.ofNat 64 call.nb)
      hcallInv hcallLive hrequest.requestNonnegative
      (fun _ => hrequest.requestWithinLimit)
  have hallocatedMode :
    SortSlice.ValuesModeInvariant (mergeHiAllocated call).state.a.hasValues
      (mergeHiAllocated call).state.data := by
    simpa only [hallocPost.valuesMode, hallocPost.data_eq] using hcallMode
  have htempRange : TempRangeInBounds (mergeHiAllocated call).state.a 0
    call.nb := by
    constructor
    · omega
    · simp only [zero_add]
      apply Int.ofNat_le.mpr
      rw [hallocPost.logicalCapacity]
      simpa only [hrequest.requestRoundtrip] using hallocPost.requestFits
  have hmainRange : SortSlice.RangeInBounds
    (mergeHiAllocated call).state.data call.ssb call.nb := by
    constructor
    · exact hgeometry.ssbNonnegative
    · rw [hallocPost.data_eq]
      exact hgeometry.rightRange
  rcases mainToTempMemcpyTraced_post (.hi .initialDataToTemp)
    mergeHiInitialDataToTempPermit call.nb (mergeHiAllocated call).state 0
    call.ssb htempRange hmainRange hallocPost.invariant hallocPost.live
    hallocatedMode with ⟨copied, hcopy⟩
  have hfull : MergeHiCursorInvariant (mergeHiAllocated call).state call.nb
    (mergeHiFullCursor call copied) := by
    refine
      { baseNonnegative := hgeometry.ssaNonnegative
        ssaEquation := ?_
        ssbEquation := ?_
        destEquation := ?_
        mainRange := ?_
        leftWordBound := ?_
        rightWordBound := ?_
        tempCapacity := ?_
        tempValuesMode := ?_
        tempInvariant := hcopy.tempInvariant
        tempLive := hcopy.tempLive
        requestFits := ?_
        valuesMode := hcopy.valuesMode
        stableFrame := MergeHiStableFrame.of_movement hcopy.frame
        storageFrame := MergeHiStorageFrame.of_movement hcopy.frame }
    · change call.ssa + Int.ofNat (call.na - 1) + 1 =
      call.ssa + Int.ofNat call.na
      simp only [Int.ofNat_eq_natCast, Nat.cast_sub hgeometry.leftPositive]
      omega
    · change Int.ofNat (call.nb - 1) + 1 = Int.ofNat call.nb
      simp only [Int.ofNat_eq_natCast, Nat.cast_sub hgeometry.rightPositive]
      omega
    · change call.ssb + Int.ofNat (call.nb - 1) + 1 =
      call.ssa + Int.ofNat (call.na + call.nb)
      have hadjacent := hgeometry.adjacent
      simp only [Int.ofNat_eq_natCast, Nat.cast_add,
        Nat.cast_sub hgeometry.rightPositive] at hadjacent ⊢
      omega
    · change call.ssa + Int.ofNat (call.na + call.nb) ≤
      Int.ofNat copied.data.entries.size
      rwa [hcopy.frame.dataSize, hallocPost.data_eq]
    · change call.na ≤ PY_LIST_MAX
      have hrun := hgeometry.runLengthBound
      omega
    · change call.nb ≤ PY_LIST_MAX
      have hrun := hgeometry.runLengthBound
      omega
    · change call.nb ≤ copied.a.cells.size
      rw [hcopy.frame.tempSize, hallocPost.logicalCapacity]
      simpa only [hrequest.requestRoundtrip] using hallocPost.requestFits
    · simpa [mergeHiFullCursor] using hcopy.tempValuesMode
    · change call.nb ≤ copied.alloced.toNat
      rw [hcopy.frame.alloced]
      simpa only [hrequest.requestRoundtrip] using hallocPost.requestFits
  rcases mergeHiCopyDataDecrTraced_safe (mergeHiAllocated call).state call.nb
    (mergeHiFullCursor call copied) hfull hgeometry.leftPositive with
    ⟨forced, hforced, hforcedSafe, hforcedInv, _hdst, _hsrc⟩
  have hinitial : MergeHiCursorInvariant (mergeHiAllocated call).state call.nb
    (mergeHiInitialCursor call forced) := by
    simpa [mergeHiInitialCursor, mergeHiFullCursor] using
      hforcedInv.setControl forced.state.min_gallop (.straight 0 0)
  have hinitialFuel : MergeHiFuelInvariant (call.na + call.nb)
    (mergeHiInitialCursor call forced) := by
    unfold MergeHiFuelInvariant
    simp only [mergeHiInitialCursor]
    have hna := hgeometry.leftPositive
    omega
  refine ⟨copied, forced,
    { requestFacts := hrequest
      geometry := hgeometry
      inputTempInvariant := hcallInv
      inputTempLive := hcallLive
      inputValuesMode := hcallMode
      directionalDispatch := hdispatch
      allocation := hallocPost
      initialCopy := hcopy
      forcedResult := ?_
      forcedSafe := ?_
      initialInvariant := hinitial
      initialFuel := hinitialFuel }⟩
  · simpa [mergeHiFullCursor] using hforced
  · simpa [mergeHiFullCursor] using hforcedSafe

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHi_observables](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
through the exact entry equation exported by `mergeHi_lockstep`. -/
private lemma mergeHi_observables
  (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
  (copied : MergeState κ ν) (forced : MergeHiDataCursorResult κ ν)
  (result : MergeHiResult κ ν)
  (hprepared : MergeHiPrepared pre scanned i call copied forced)
  (hlockstep : MergeHiLockstepPost call copied result) :
  MergeHiObservablePost call result := by
  have hcopy := hprepared.initialCopy
  have hgeometry := hprepared.geometry
  have hinputEvent :
    (mergeHiTraced? call.state call.ssa call.ssb call.na
      call.nb).trace.HasAccess .read .inputKeys := by
    have hprefixed := mergeHiHasAccess_bind_left
      (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
        mergeHiInitialDataToTempPermit call.nb
        (mergeHiAllocated call).state 0 call.ssb)
      (mergeHiTracedAfterCopy call) .read .inputKeys
      (hcopy.inputKeyEvent hgeometry.rightPositive)
    rwa [hlockstep.tracedEntry]
  have htempWriteEvent :
    (mergeHiTraced? call.state call.ssa call.ssb call.na
      call.nb).trace.HasTempAccess .write := by
    have hprefixed := mergeHiHasTempAccess_bind_left
      (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
        mergeHiInitialDataToTempPermit call.nb
        (mergeHiAllocated call).state 0 call.ssb)
      (mergeHiTracedAfterCopy call) .write
      (hcopy.tempWriteEvent hgeometry.rightPositive)
    rwa [hlockstep.tracedEntry]
  have htempReadEvent :
    (mergeHiTraced? call.state call.ssa call.ssb call.na
      call.nb).trace.HasTempAccess .read := by
    have hprefixed := mergeHiHasTempAccess_bind_right
      (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
        mergeHiInitialDataToTempPermit call.nb
        (mergeHiAllocated call).state 0 call.ssb)
      (mergeHiTracedAfterCopy call) copied .read hcopy.success
      hlockstep.afterCopyRead
    rwa [hlockstep.tracedEntry]
  refine
    { core := hlockstep.core
      memcpyProvenance := hcopy.provenanceContract
      inputKeyEvent := hinputEvent
      tempWriteEvent := htempWriteEvent
      tempReadEvent := htempReadEvent
      synchronizedValuesEvent := ?_ }
  intro hvalues
  have hallocatedValues : (mergeHiAllocated call).state.a.hasValues = true :=
    hprepared.allocation.valuesMode.trans hvalues
  have hprefixed := mergeHiHasAccess_bind_left
    (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
      mergeHiInitialDataToTempPermit call.nb
      (mergeHiAllocated call).state 0 call.ssb)
    (mergeHiTracedAfterCopy call) .read .synchronizedValues
    (hcopy.synchronizedValuesEvent hgeometry.rightPositive hallocatedValues)
  rwa [hlockstep.tracedEntry]

end CPythonListsort

/--
[mergeHiInitialDataToTempPermit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiInitialDataToTempPermit_eq
  {κ : Type u}
  {ν : Type v} :
-- imply
  (MergeMemcpySite.hi .initialDataToTemp).MainToTempPermit := by
-- proof
  apply CPythonListsort.mergeHiInitialDataToTempPermit

/--
[mergeHiGallopTempToDataPermit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiGallopTempToDataPermit_eq
  {κ : Type u}
  {ν : Type v} :
-- imply
  (MergeMemcpySite.hi .gallopTempToData).TempToMainPermit := by
-- proof
  apply CPythonListsort.mergeHiGallopTempToDataPermit

/--
[mergeHiFinalTempToDataPermit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHiFinalTempToDataPermit_eq
  {κ : Type u}
  {ν : Type v} :
-- imply
  (MergeMemcpySite.hi .finalTempToData).TempToMainPermit := by
-- proof
  apply CPythonListsort.mergeHiFinalTempToDataPermit

/--
[erase_mergeHiGallopRoundTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma erase_mergeHiGallopRoundTraced_eq
  {κ : Type u}
  {ν : Type v}
  {cursor : MergeHiCursor κ ν}
  {nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν)}
  {next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)}
-- given
  (hNext : ∀ cursor, (nextTraced cursor).erase = next cursor) :
-- imply
  (mergeHiGallopRoundTraced? cursor nextTraced).erase = mergeHiGallopRound? cursor next := by
-- proof
  apply CPythonListsort.erase_mergeHiGallopRoundTraced cursor nextTraced next hNext

/--
[mergeHi_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean)
-/
@[path]
private lemma mergeHi_safe_eq
  {κ : Type u}
  {ν : Type v}
  {pre : MergeState κ ν}
  {scanned i : Nat}
  {call : MergeAtCall κ ν}
-- given
  (hlayout : PendingLayout pre scanned)
  (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
  (hprepare : prepareMergeAt? pre i = some (.mergeHi call))
  (hInv : TempStorageInv pre.a pre.alloced)
  (hLive : pre.a.Live)
  (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data) :
-- imply
  ∃ result, MergeHiSafetyPost pre scanned i call (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb) result := by
-- proof
  apply CPythonListsort.mergeHi_safe pre scanned i call hlayout hmax hprepare hInv hLive hMode


-- created on 2026-10-23

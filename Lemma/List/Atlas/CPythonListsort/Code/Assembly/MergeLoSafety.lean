import Mathlib
import sympy.Basic
import Structure.CPythonListsort.Code.Assembly.MergeLoSafety.Part4
open CPythonListsort CPythonListsort.MergeLoStableFrame CPythonListsort.MergeLoStorageFrame CPythonListsort.MergeLoMachineInvariant


namespace CPythonListsort

/--
[mergeLoTraceOption_erase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma mergeLoTraceOption_erase
  {κ : Type u}
  {ν : Type v}
  {value : Option α} :
-- imply
  (mergeLoTraceOption value).erase = value := by
-- proof
  cases value <;> rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeTempRead_ofNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma mergeTempRead_ofNat
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {index : Nat} :
-- imply
  mergeTempRead? storage (Int.ofNat index) = mergeLoTempRead? storage index := by
-- proof
  simp [mergeTempRead?, mergeLoTempRead?]

end CPythonListsort

namespace CPythonListsort

/--
[mergeTempWrite_ofNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma mergeTempWrite_ofNat
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {index : Nat}
  {entry : SortSliceEntry κ ν} :
-- imply
  mergeTempWrite? storage (Int.ofNat index) entry = mergeLoTempWrite? storage index entry := by
-- proof
  by_cases hindex : index < storage.cells.size
  · simp [mergeTempWrite?, mergeLoTempWrite?, hindex,
    Array.setIfInBounds_def]
  · simp [mergeTempWrite?, mergeLoTempWrite?, hindex]

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempCell_ofNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma mainToTempCell_ofNat
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {destination : Nat}
  {source : Int} :
-- imply
  mainToTempCell? state (Int.ofNat destination) source = (do let entry ← state.data.read? source let storage ← mergeLoTempWrite? state.a destination entry pure { state with a := storage }) := by
-- proof
  unfold mainToTempCell?
  cases hread : state.data.read? source with
  | none => rfl
  | some entry =>
    simp only [bind, Option.bind]
    rw [show mergeTempWrite? state.a (Int.ofNat destination) entry =
      mergeLoTempWrite? state.a destination entry from
        mergeTempWrite_ofNat state.a destination entry]

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainCell_ofNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma tempToMainCell_ofNat
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {destination : Int}
  {source : Nat} :
-- imply
  tempToMainCell? state destination (Int.ofNat source) = (do let entry ← mergeLoTempRead? state.a source let data ← state.data.write? destination entry pure { state with data := data }) := by
-- proof
  unfold tempToMainCell?
  rw [show mergeTempRead? state.a (Int.ofNat source) =
    mergeLoTempRead? state.a source from mergeTempRead_ofNat state.a source]

end CPythonListsort

namespace CPythonListsort

/--
[mainToTempMemcpy_eq_mergeLo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma mainToTempMemcpy_eq_mergeLo
  {κ : Type u}
  {ν : Type v}
  {site : MergeLoMemcpyCallsite}
  {count : Nat}
  {state : MergeState κ ν}
  {destination : Nat}
  {source : Int}
-- given
  (hDirection : site.backings = { destination := .temporary, source := .main }) :
-- imply
  mainToTempMemcpy? count state (Int.ofNat destination) source = mergeLoMemcpyDataToTemp? site hDirection count state destination source := by
-- proof
  induction count generalizing state destination source with
  | zero => rfl
  | succ count ih =>
    simp only [mainToTempMemcpy?, mergeLoMemcpyDataToTemp?]
    rw [mainToTempCell_ofNat]
    cases hread : state.data.read? source with
    | none => simp
    | some entry =>
      cases hwrite : mergeLoTempWrite? state.a destination entry with
      | none => simp [hwrite]
      | some storage =>
        simpa [hread, hwrite, bind, Option.bind,
          Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] using
          ih { state with a := storage } (destination + 1) (source + 1)

end CPythonListsort

namespace CPythonListsort

/--
[tempToMainMemcpy_eq_mergeLo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma tempToMainMemcpy_eq_mergeLo
  {κ : Type u}
  {ν : Type v}
  {site : MergeLoMemcpyCallsite}
  {count : Nat}
  {state : MergeState κ ν}
  {destination : Int}
  {source : Nat}
-- given
  (hDirection : site.backings = { destination := .main, source := .temporary }) :
-- imply
  tempToMainMemcpy? count state destination (Int.ofNat source) = mergeLoMemcpyTempToData? site hDirection count state destination source := by
-- proof
  induction count generalizing state destination source with
  | zero => rfl
  | succ count ih =>
    simp only [tempToMainMemcpy?, mergeLoMemcpyTempToData?]
    rw [tempToMainCell_ofNat]
    cases hread : mergeLoTempRead? state.a source with
    | none => simp
    | some entry =>
      cases hwrite : state.data.write? destination entry with
      | none => simp [hwrite]
      | some data =>
        simpa [hread, hwrite, bind, Option.bind,
          Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] using
          ih { state with data := data } (destination + 1) (source + 1)

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoTemporary_validRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma mergeLoTemporary_validRange
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {start count : Nat}
-- given
  (hbound : start + count ≤ storage.cells.size)
  (hinitialized : MergeLoTempRangeInitialized storage start count) :
-- imply
  (GallopKeySource.temporary storage (Int.ofNat start)).ValidRange count := by
-- proof
  refine ⟨Int.natCast_nonneg start, ?_, ?_⟩
  · simpa only [GallopKeySource.base, GallopKeySource.extent,
    Int.ofNat_eq_natCast, Nat.cast_add] using Int.ofNat_le.mpr hbound
  · intro i hi
    obtain ⟨entry, hentry⟩ := hinitialized i hi
    refine ⟨entry, ?_⟩
    change mergeTempRead? storage
      (Int.ofNat start + Int.ofNat i) = some entry
    rw [show Int.ofNat start + Int.ofNat i = Int.ofNat (start + i) by
      simp only [Int.ofNat_eq_natCast, Nat.cast_add]]
    rwa [mergeTempRead_ofNat]

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeLoTemporaryGallopRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma erase_mergeLoTemporaryGallopRight
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {start count : Nat}
  {slice : SortSlice κ ν}
  {key : κ}
-- given
  (hbound : start + count ≤ state.a.cells.size)
  (hinitialized : MergeLoTempRangeInitialized state.a start count)
  (hslice : mergeLoTempRun? state.a start count = some slice)
  (hcount : 0 < count)
  (hmax : count ≤ PY_LIST_MAX) :
-- imply
  (gallopRightTraced? state (.temporary state.a (Int.ofNat start)) key count 0).erase = gallopRight? state slice 0 key count 0 := by
-- proof
  apply erase_gallopRightTraced_eq_slice state
    (.temporary state.a (Int.ofNat start)) slice 0 key count 0
  · exact mergeLoTemporary_validRange state.a start count hbound hinitialized
  · exact tempRun_agreesWithSlice_of_eq_some state.a start count slice hslice
  · exact hcount
  · omega
  · exact hmax

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_pure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_pure (value : α) :
  MergeLoMemoryEventFree (TraceResult.pure value) :=
⟨rfl, rfl⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_failure :
  MergeLoMemoryEventFree (TraceResult.failure : TraceResult α) :=
⟨rfl, rfl⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_map (current : TraceResult α)
  (transform : α → β) (hcurrent : MergeLoMemoryEventFree current) :
  MergeLoMemoryEventFree (current.map transform) :=
  hcurrent

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_bind (current : TraceResult α)
  (next : α → TraceResult β) (hcurrent : MergeLoMemoryEventFree current)
  (hnext : ∀ value, MergeLoMemoryEventFree (next value)) :
  MergeLoMemoryEventFree (current.bind next) := by
  exact
    ⟨TraceResult.memoryEvents_bind_eq_nil current next hcurrent.1
      (fun value => (hnext value).1),
      TraceResult.policyEvents_bind_eq_nil current next hcurrent.2
        (fun value => (hnext value).2)⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_markFuelExhausted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_markFuelExhausted
  (current : TraceResult α) (hcurrent : MergeLoMemoryEventFree current) :
  MergeLoMemoryEventFree current.markFuelExhausted := by
  simpa [MergeLoMemoryEventFree, TraceResult.markFuelExhausted,
    AccessTrace.compose, AccessTrace.exhausted] using hcurrent

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_sourceRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_sourceRead
  (source : GallopKeySource κ ν) (index : Int) :
  MergeLoMemoryEventFree (source.readTraced? index) := by
  simp [MergeLoMemoryEventFree, GallopKeySource.trace_readTraced,
    AccessTrace.singletonAccess]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_tempRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_tempRead
  (storage : TempStorage κ ν) (index : Int) :
  MergeLoMemoryEventFree (TraceResult.tempPayloadRead? storage index) := by
  unfold MergeLoMemoryEventFree
  rw [TraceResult.trace_tempPayloadRead]
  exact ⟨rfl, rfl⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_tempWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_tempWrite
  (storage : TempStorage κ ν) (index : Int)
  (entry : SortSliceEntry κ ν) :
  MergeLoMemoryEventFree
    (TraceResult.tempPayloadWrite? storage index entry) :=
⟨rfl, rfl⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_keyRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_keyRead
  (slice : SortSlice κ ν) (index : Int) :
  MergeLoMemoryEventFree (TraceResult.sortSliceKeysRead? slice index) :=
⟨rfl, rfl⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_valueRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_valueRead
  (slice : SortSlice κ ν) (index : Int) :
  MergeLoMemoryEventFree (TraceResult.sortSliceValuesRead? slice index) :=
⟨rfl, rfl⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_keyWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_keyWrite
  (slice : SortSlice κ ν) (index : Int) (entry : SortSliceEntry κ ν) :
  MergeLoMemoryEventFree
    (TraceResult.sortSliceKeysWrite? slice index entry) :=
⟨rfl, rfl⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_valueWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_valueWrite
  (slice : SortSlice κ ν) (index : Int) (entry : SortSliceEntry κ ν) :
  MergeLoMemoryEventFree
    (TraceResult.sortSliceValuesWrite? slice index entry) :=
⟨rfl, rfl⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_copyKeys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_copyKeys
  (destination source : SortSlice κ ν) (dst src : Int) :
  MergeLoMemoryEventFree
    (SortSlice.copyKeysFromTraced? destination source dst src) := by
  apply mergeLoMemoryEventFree_bind
  · exact mergeLoMemoryEventFree_keyRead _ _
  · intro entry
    exact mergeLoMemoryEventFree_keyWrite _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_copyValues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_copyValues
  (destination source : SortSlice κ ν) (dst src : Int) :
  MergeLoMemoryEventFree
    (SortSlice.copyValuesFromTraced? destination source dst src) := by
  apply mergeLoMemoryEventFree_bind
  · exact mergeLoMemoryEventFree_valueRead _ _
  · intro entry
    exact mergeLoMemoryEventFree_valueWrite _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_mainToTempKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_mainToTempKey
  (state : MergeState κ ν) (tempDst mainSrc : Int) :
  MergeLoMemoryEventFree (mainToTempKeyTraced? state tempDst mainSrc) := by
  unfold mainToTempKeyTraced?
  apply mergeLoMemoryEventFree_bind
  · exact mergeLoMemoryEventFree_keyRead _ _
  · intro entry
    apply mergeLoMemoryEventFree_map
    exact mergeLoMemoryEventFree_tempWrite _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_mainToTempValues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_mainToTempValues
  (state : MergeState κ ν) (tempDst mainSrc : Int) :
  MergeLoMemoryEventFree (mainToTempValuesTraced? state tempDst mainSrc) := by
  unfold mainToTempValuesTraced?
  apply mergeLoMemoryEventFree_bind
  · exact mergeLoMemoryEventFree_valueRead _ _
  · intro entry
    apply mergeLoMemoryEventFree_map
    exact mergeLoMemoryEventFree_tempWrite _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_tempToMainKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_tempToMainKey
  (state : MergeState κ ν) (mainDst tempSrc : Int) :
  MergeLoMemoryEventFree (tempToMainKeyTraced? state mainDst tempSrc) := by
  unfold tempToMainKeyTraced?
  apply mergeLoMemoryEventFree_bind
  · exact mergeLoMemoryEventFree_tempRead _ _
  · intro entry
    apply mergeLoMemoryEventFree_map
    exact mergeLoMemoryEventFree_keyWrite _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_tempToMainValues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_tempToMainValues
  (state : MergeState κ ν) (mainDst tempSrc : Int) :
  MergeLoMemoryEventFree (tempToMainValuesTraced? state mainDst tempSrc) := by
  unfold tempToMainValuesTraced?
  apply mergeLoMemoryEventFree_bind
  · exact mergeLoMemoryEventFree_tempRead _ _
  · intro entry
    apply mergeLoMemoryEventFree_map
    exact mergeLoMemoryEventFree_valueWrite _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_tempToMainCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_tempToMainCell
  (state : MergeState κ ν) (mainDst tempSrc : Int) :
  MergeLoMemoryEventFree (tempToMainCellTraced? state mainDst tempSrc) := by
  unfold tempToMainCellTraced?
  apply mergeLoMemoryEventFree_bind
  · exact mergeLoMemoryEventFree_tempToMainKey _ _ _
  · intro keyResult
    split
    · exact mergeLoMemoryEventFree_tempToMainValues _ _ _
    · exact mergeLoMemoryEventFree_pure _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_mainToTempKeys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_mainToTempKeys
  (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
  (state : MergeState κ ν) (tempDst mainSrc : Int) :
  MergeLoMemoryEventFree
    (mainToTempKeysTraced? site permit count state tempDst mainSrc) := by
  induction count generalizing state tempDst mainSrc with
  | zero => exact mergeLoMemoryEventFree_pure _
  | succ count ih =>
    simp only [mainToTempKeysTraced?]
    apply mergeLoMemoryEventFree_bind
    · exact mergeLoMemoryEventFree_mainToTempKey _ _ _
    · intro nextState
      exact ih _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_mainToTempValuesPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_mainToTempValuesPhase
  (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
  (state : MergeState κ ν) (tempDst mainSrc : Int) :
  MergeLoMemoryEventFree
    (mainToTempValuesPhaseTraced? site permit count state tempDst mainSrc) := by
  induction count generalizing state tempDst mainSrc with
  | zero => exact mergeLoMemoryEventFree_pure _
  | succ count ih =>
    simp only [mainToTempValuesPhaseTraced?]
    apply mergeLoMemoryEventFree_bind
    · exact mergeLoMemoryEventFree_mainToTempValues _ _ _
    · intro nextState
      exact ih _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_mainToTempMemcpy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_mainToTempMemcpy
  (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
  (state : MergeState κ ν) (tempDst mainSrc : Int) :
  MergeLoMemoryEventFree
    (mainToTempMemcpyTraced? site permit count state tempDst mainSrc) := by
  unfold mainToTempMemcpyTraced?
  apply mergeLoMemoryEventFree_bind
  · exact mergeLoMemoryEventFree_mainToTempKeys _ _ _ _ _ _
  · intro keyResult
    split
    · exact mergeLoMemoryEventFree_mainToTempValuesPhase _ _ _ _ _ _
    · exact mergeLoMemoryEventFree_pure _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_tempToMainKeys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_tempToMainKeys
  (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
  (state : MergeState κ ν) (mainDst tempSrc : Int) :
  MergeLoMemoryEventFree
    (tempToMainKeysTraced? site permit count state mainDst tempSrc) := by
  induction count generalizing state mainDst tempSrc with
  | zero => exact mergeLoMemoryEventFree_pure _
  | succ count ih =>
    simp only [tempToMainKeysTraced?]
    apply mergeLoMemoryEventFree_bind
    · exact mergeLoMemoryEventFree_tempToMainKey _ _ _
    · intro nextState
      exact ih _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_tempToMainValuesPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_tempToMainValuesPhase
  (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
  (state : MergeState κ ν) (mainDst tempSrc : Int) :
  MergeLoMemoryEventFree
    (tempToMainValuesPhaseTraced? site permit count state mainDst tempSrc) := by
  induction count generalizing state mainDst tempSrc with
  | zero => exact mergeLoMemoryEventFree_pure _
  | succ count ih =>
    simp only [tempToMainValuesPhaseTraced?]
    apply mergeLoMemoryEventFree_bind
    · exact mergeLoMemoryEventFree_tempToMainValues _ _ _
    · intro nextState
      exact ih _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_tempToMainMemcpy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_tempToMainMemcpy
  (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
  (state : MergeState κ ν) (mainDst tempSrc : Int) :
  MergeLoMemoryEventFree
    (tempToMainMemcpyTraced? site permit count state mainDst tempSrc) := by
  unfold tempToMainMemcpyTraced?
  apply mergeLoMemoryEventFree_bind
  · exact mergeLoMemoryEventFree_tempToMainKeys _ _ _ _ _ _
  · intro keyResult
    split
    · exact mergeLoMemoryEventFree_tempToMainValuesPhase _ _ _ _ _ _
    · exact mergeLoMemoryEventFree_pure _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_memmoveForwardKeys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_memmoveForwardKeys
  (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
  MergeLoMemoryEventFree
    (SortSlice.memmoveForwardKeysTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact mergeLoMemoryEventFree_pure _
  | succ count ih =>
    simp only [SortSlice.memmoveForwardKeysTraced?]
    apply mergeLoMemoryEventFree_bind
    · exact mergeLoMemoryEventFree_copyKeys _ _ _ _
    · intro updated
      exact ih _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_memmoveForwardValues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_memmoveForwardValues
  (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
  MergeLoMemoryEventFree
    (SortSlice.memmoveForwardValuesTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact mergeLoMemoryEventFree_pure _
  | succ count ih =>
    simp only [SortSlice.memmoveForwardValuesTraced?]
    apply mergeLoMemoryEventFree_bind
    · exact mergeLoMemoryEventFree_copyValues _ _ _ _
    · intro updated
      exact ih _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_memmoveBackwardKeys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_memmoveBackwardKeys
  (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
  MergeLoMemoryEventFree
    (SortSlice.memmoveBackwardKeysTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact mergeLoMemoryEventFree_pure _
  | succ count ih =>
    simp only [SortSlice.memmoveBackwardKeysTraced?]
    apply mergeLoMemoryEventFree_bind
    · exact mergeLoMemoryEventFree_copyKeys _ _ _ _
    · intro updated
      exact ih _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_memmoveBackwardValues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_memmoveBackwardValues
  (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
  MergeLoMemoryEventFree
    (SortSlice.memmoveBackwardValuesTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact mergeLoMemoryEventFree_pure _
  | succ count ih =>
    simp only [SortSlice.memmoveBackwardValuesTraced?]
    apply mergeLoMemoryEventFree_bind
    · exact mergeLoMemoryEventFree_copyValues _ _ _ _
    · intro updated
      exact ih _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_memmove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_memmove
  (valuesPresent : Bool) (slice : SortSlice κ ν)
  (dst src : Int) (count : Nat) :
  MergeLoMemoryEventFree
    (SortSlice.memmoveTraced? valuesPresent slice dst src count) := by
  unfold SortSlice.memmoveTraced?
  split
  · apply mergeLoMemoryEventFree_bind
    · exact mergeLoMemoryEventFree_memmoveForwardKeys _ _ _ _
    · intro keyResult
      split
      · exact mergeLoMemoryEventFree_memmoveForwardValues _ _ _ _
      · constructor <;> rfl
  · apply mergeLoMemoryEventFree_bind
    · exact mergeLoMemoryEventFree_memmoveBackwardKeys _ _ _ _
    · intro keyResult
      split
      · exact mergeLoMemoryEventFree_memmoveBackwardValues _ _ _ _
      · constructor <;> rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_mainDataMemmove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_mainDataMemmove
  (state : MergeState κ ν) (dst src : Int) (count : Nat) :
  MergeLoMemoryEventFree (mainDataMemmoveTraced? state dst src count) := by
  unfold mainDataMemmoveTraced?
  apply mergeLoMemoryEventFree_map
  exact mergeLoMemoryEventFree_memmove _ _ _ _ _
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_leftRightExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_leftRightExponential
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (hint maxOffset lastOffset offset : Nat) :
  MergeLoMemoryEventFree
    (gallopLeftRightExponentialTraced? fuel lt source key hint maxOffset
      lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
    by_cases hfuel : offset < maxOffset <;>
      simp [gallopLeftRightExponentialTraced?, MergeLoMemoryEventFree,
        hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
    simp only [gallopLeftRightExponentialTraced?]
    split
    · apply mergeLoMemoryEventFree_bind
      · exact mergeLoMemoryEventFree_sourceRead _ _
      · intro entry
        split
        · split
          · exact ih _ _
          · exact mergeLoMemoryEventFree_failure
        · exact mergeLoMemoryEventFree_pure _
    · exact mergeLoMemoryEventFree_pure _
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_leftLeftExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_leftLeftExponential
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (hint maxOffset lastOffset offset : Nat) :
  MergeLoMemoryEventFree
    (gallopLeftLeftExponentialTraced? fuel lt source key hint maxOffset
      lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
    by_cases hfuel : offset < maxOffset <;>
      simp [gallopLeftLeftExponentialTraced?, MergeLoMemoryEventFree,
        hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
    simp only [gallopLeftLeftExponentialTraced?]
    split
    · apply mergeLoMemoryEventFree_bind
      · exact mergeLoMemoryEventFree_sourceRead _ _
      · intro entry
        split
        · exact mergeLoMemoryEventFree_pure _
        · split
          · exact ih _ _
          · exact mergeLoMemoryEventFree_failure
    · exact mergeLoMemoryEventFree_pure _
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_rightLeftExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_rightLeftExponential
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (hint maxOffset lastOffset offset : Nat) :
  MergeLoMemoryEventFree
    (gallopRightLeftExponentialTraced? fuel lt source key hint maxOffset
      lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
    by_cases hfuel : offset < maxOffset <;>
      simp [gallopRightLeftExponentialTraced?, MergeLoMemoryEventFree,
        hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
    simp only [gallopRightLeftExponentialTraced?]
    split
    · apply mergeLoMemoryEventFree_bind
      · exact mergeLoMemoryEventFree_sourceRead _ _
      · intro entry
        split
        · split
          · exact ih _ _
          · exact mergeLoMemoryEventFree_failure
        · exact mergeLoMemoryEventFree_pure _
    · exact mergeLoMemoryEventFree_pure _
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_rightRightExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_rightRightExponential
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (hint maxOffset lastOffset offset : Nat) :
  MergeLoMemoryEventFree
    (gallopRightRightExponentialTraced? fuel lt source key hint maxOffset
      lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
    by_cases hfuel : offset < maxOffset <;>
      simp [gallopRightRightExponentialTraced?, MergeLoMemoryEventFree,
        hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
    simp only [gallopRightRightExponentialTraced?]
    split
    · apply mergeLoMemoryEventFree_bind
      · exact mergeLoMemoryEventFree_sourceRead _ _
      · intro entry
        split
        · exact mergeLoMemoryEventFree_pure _
        · split
          · exact ih _ _
          · exact mergeLoMemoryEventFree_failure
    · exact mergeLoMemoryEventFree_pure _
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_leftBinary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_leftBinary
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (lower upper : Nat) :
  MergeLoMemoryEventFree
    (gallopLeftBinaryTraced? fuel lt source key lower upper) := by
  induction fuel generalizing lower upper with
  | zero =>
    by_cases hfuel : lower < upper <;>
      simp [gallopLeftBinaryTraced?, MergeLoMemoryEventFree, hfuel] <;>
        (constructor <;> rfl)
  | succ fuel ih =>
    simp only [gallopLeftBinaryTraced?]
    split
    · apply mergeLoMemoryEventFree_bind
      · exact mergeLoMemoryEventFree_sourceRead _ _
      · intro entry
        split
        · exact ih _ _
        · exact ih _ _
    · exact mergeLoMemoryEventFree_pure _
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_rightBinary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_rightBinary
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (lower upper : Nat) :
  MergeLoMemoryEventFree
    (gallopRightBinaryTraced? fuel lt source key lower upper) := by
  induction fuel generalizing lower upper with
  | zero =>
    by_cases hfuel : lower < upper <;>
      simp [gallopRightBinaryTraced?, MergeLoMemoryEventFree, hfuel] <;>
        (constructor <;> rfl)
  | succ fuel ih =>
    simp only [gallopRightBinaryTraced?]
    split
    · apply mergeLoMemoryEventFree_bind
      · exact mergeLoMemoryEventFree_sourceRead _ _
      · intro entry
        split
        · exact ih _ _
        · exact ih _ _
    · exact mergeLoMemoryEventFree_pure _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_finishLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_finishLeft
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (n : Nat) (lastOffset upperOffset : Int)
  (exponentialFuelExhausted : Bool) :
  MergeLoMemoryEventFree
    (finishGallopLeftTraced? fuel lt source key n lastOffset upperOffset
      exponentialFuelExhausted) := by
  unfold finishGallopLeftTraced?
  split
  · dsimp only
    split
    · split
      · constructor <;> rfl
      · exact mergeLoMemoryEventFree_leftBinary _ _ _ _ _ _
    · exact mergeLoMemoryEventFree_failure
  · exact mergeLoMemoryEventFree_failure

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_finishRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_finishRight
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (n : Nat) (lastOffset upperOffset : Int)
  (exponentialFuelExhausted : Bool) :
  MergeLoMemoryEventFree
    (finishGallopRightTraced? fuel lt source key n lastOffset upperOffset
      exponentialFuelExhausted) := by
  unfold finishGallopRightTraced?
  split
  · dsimp only
    split
    · split
      · constructor <;> rfl
      · exact mergeLoMemoryEventFree_rightBinary _ _ _ _ _ _
    · exact mergeLoMemoryEventFree_failure
  · exact mergeLoMemoryEventFree_failure

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_gallopLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_gallopLeft
  (state : MergeState κ ν) (source : GallopKeySource κ ν)
  (key : κ) (n hint : Nat) :
  MergeLoMemoryEventFree (gallopLeftTraced? state source key n hint) := by
  unfold gallopLeftTraced?
  split
  · apply mergeLoMemoryEventFree_bind
    · exact mergeLoMemoryEventFree_sourceRead _ _
    · intro hinted
      split
      · apply mergeLoMemoryEventFree_bind
        · exact mergeLoMemoryEventFree_leftRightExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact mergeLoMemoryEventFree_finishLeft _ _ _ _ _ _ _ _
      · apply mergeLoMemoryEventFree_bind
        · exact mergeLoMemoryEventFree_leftLeftExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact mergeLoMemoryEventFree_finishLeft _ _ _ _ _ _ _ _
  · exact mergeLoMemoryEventFree_failure

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_gallopRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_gallopRight
  (state : MergeState κ ν) (source : GallopKeySource κ ν)
  (key : κ) (n hint : Nat) :
  MergeLoMemoryEventFree (gallopRightTraced? state source key n hint) := by
  unfold gallopRightTraced?
  split
  · apply mergeLoMemoryEventFree_bind
    · exact mergeLoMemoryEventFree_sourceRead _ _
    · intro hinted
      split
      · apply mergeLoMemoryEventFree_bind
        · exact mergeLoMemoryEventFree_rightLeftExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact mergeLoMemoryEventFree_finishRight _ _ _ _ _ _ _ _
      · apply mergeLoMemoryEventFree_bind
        · exact mergeLoMemoryEventFree_rightRightExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact mergeLoMemoryEventFree_finishRight _ _ _ _ _ _ _ _
  · exact mergeLoMemoryEventFree_failure

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_traceOption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_traceOption (value : Option α) :
  MergeLoMemoryEventFree (mergeLoTraceOption value) := by
  cases value
  · exact mergeLoMemoryEventFree_failure
  · exact mergeLoMemoryEventFree_pure _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_fuelFailure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_fuelFailure
  (machine : MergeLoMachine κ ν) :
  MergeLoMemoryEventFree (mergeLoFuelFailureTraced machine) := by
  apply mergeLoMemoryEventFree_markFuelExhausted
  exact mergeLoMemoryEventFree_pure _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_copyAIncr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_copyAIncr
  (machine : MergeLoMachine κ ν) :
  MergeLoMemoryEventFree (mergeLoCopyAIncrTraced? machine) := by
  unfold mergeLoCopyAIncrTraced?
  apply mergeLoMemoryEventFree_map
  exact mergeLoMemoryEventFree_tempToMainCell _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_copyBIncr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_copyBIncr
  (machine : MergeLoMachine κ ν) :
  MergeLoMemoryEventFree (mergeLoCopyBIncrTraced? machine) := by
  unfold mergeLoCopyBIncrTraced?
  apply mergeLoMemoryEventFree_map
  exact mergeLoMemoryEventFree_mainDataMemmove _ _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_succeed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_succeed
  (machine : MergeLoMachine κ ν) :
  MergeLoMemoryEventFree (mergeLoSucceedTraced? machine) := by
  unfold mergeLoSucceedTraced?
  apply mergeLoMemoryEventFree_map
  exact mergeLoMemoryEventFree_tempToMainMemcpy _ _ _ _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_copyB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_copyB
  (machine : MergeLoMachine κ ν) :
  MergeLoMemoryEventFree (mergeLoCopyBTraced? machine) := by
  unfold mergeLoCopyBTraced?
  split
  · apply mergeLoMemoryEventFree_bind
    · exact mergeLoMemoryEventFree_mainDataMemmove _ _ _ _
    · intro state
      apply mergeLoMemoryEventFree_map
      exact mergeLoMemoryEventFree_tempToMainCell _ _ _
  · exact mergeLoMemoryEventFree_failure

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_gallopRound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_gallopRound
  (machine : MergeLoMachine κ ν)
  (next : MergeLoMachine κ ν → Nat → Nat →
    TraceResult (MergeLoResult κ ν))
  (hnext : ∀ machine aCount bCount,
    MergeLoMemoryEventFree (next machine aCount bCount)) :
  MergeLoMemoryEventFree (mergeLoGallopRoundTraced? machine next) := by
  unfold mergeLoGallopRoundTraced?
  split
  · exact mergeLoMemoryEventFree_failure
  · dsimp only
    apply mergeLoMemoryEventFree_bind
    · exact mergeLoMemoryEventFree_keyRead _ _
    · intro firstB
      apply mergeLoMemoryEventFree_bind
      · exact mergeLoMemoryEventFree_traceOption _
      · intro _activeA
        apply mergeLoMemoryEventFree_bind
        · exact mergeLoMemoryEventFree_gallopRight _ _ _ _ _
        · intro gallopA
          split
          · exact mergeLoMemoryEventFree_fuelFailure _
          · split
            · exact mergeLoMemoryEventFree_failure
            · apply mergeLoMemoryEventFree_bind
              · exact mergeLoMemoryEventFree_tempToMainMemcpy _ _ _ _ _ _
              · intro state
                split
                · exact mergeLoMemoryEventFree_succeed _
                · split
                  · exact mergeLoMemoryEventFree_copyB _
                  · apply mergeLoMemoryEventFree_bind
                    · exact mergeLoMemoryEventFree_copyBIncr _
                    · intro afterB
                      split
                      · exact mergeLoMemoryEventFree_succeed _
                      · apply mergeLoMemoryEventFree_bind
                        · exact mergeLoMemoryEventFree_tempRead _ _
                        · intro firstA
                          apply mergeLoMemoryEventFree_bind
                          · exact mergeLoMemoryEventFree_gallopLeft _ _ _ _ _
                          · intro gallopB
                            split
                            · exact mergeLoMemoryEventFree_fuelFailure _
                            · split
                              · exact mergeLoMemoryEventFree_failure
                              · apply mergeLoMemoryEventFree_bind
                                · exact mergeLoMemoryEventFree_mainDataMemmove _ _ _ _
                                · intro movedState
                                  split
                                  · exact mergeLoMemoryEventFree_succeed _
                                  · apply mergeLoMemoryEventFree_bind
                                    · exact mergeLoMemoryEventFree_copyAIncr _
                                    · intro afterA
                                      split
                                      · exact mergeLoMemoryEventFree_copyB _
                                      · exact hnext _ _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemoryEventFree_loop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMemoryEventFree_loop
  (fuel : Nat) (machine : MergeLoMachine κ ν) (phase : MergeLoPhase) :
  MergeLoMemoryEventFree (mergeLoLoopTraced? fuel machine phase) := by
  induction fuel generalizing machine phase with
  | zero =>
    cases phase <;> exact mergeLoMemoryEventFree_fuelFailure _
  | succ fuel ih =>
    cases phase with
    | ordinary aCount bCount =>
      simp only [mergeLoLoopTraced?]
      split
      · exact mergeLoMemoryEventFree_failure
      · apply mergeLoMemoryEventFree_bind
        · exact mergeLoMemoryEventFree_tempRead _ _
        · intro firstA
          apply mergeLoMemoryEventFree_bind
          · exact mergeLoMemoryEventFree_keyRead _ _
          · intro firstB
            split
            · apply mergeLoMemoryEventFree_bind
              · exact mergeLoMemoryEventFree_copyBIncr _
              · intro afterB
                split
                · exact mergeLoMemoryEventFree_succeed _
                · split
                  · exact ih _ _
                  · exact ih _ _
            · apply mergeLoMemoryEventFree_bind
              · exact mergeLoMemoryEventFree_copyAIncr _
              · intro afterA
                split
                · exact mergeLoMemoryEventFree_copyB _
                · split
                  · exact ih _ _
                  · exact ih _ _
    | galloping =>
      simp only [mergeLoLoopTraced?]
      apply mergeLoMemoryEventFree_gallopRound
      intro nextMachine aCount bCount
      split
      · exact ih _ _
      · exact ih _ _

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoTraced_topLevelEvents_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoTraced_topLevelEvents_empty
  (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat) :
  MergeLoMemoryEventFree (mergeLoTraced? state ssa ssb na nb) := by
  unfold mergeLoTraced?
  split
  · dsimp only
    split
    · exact mergeLoMemoryEventFree_pure _
    · apply mergeLoMemoryEventFree_bind
      · exact mergeLoMemoryEventFree_mainToTempMemcpy _ _ _ _ _ _
      · intro copied
        apply mergeLoMemoryEventFree_bind
        · exact mergeLoMemoryEventFree_copyBIncr _
        · intro first
          split
          · exact mergeLoMemoryEventFree_succeed _
          · split
            · exact mergeLoMemoryEventFree_copyB _
            · exact mergeLoMemoryEventFree_loop _ _ _
  · exact mergeLoMemoryEventFree_failure

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoTraced_memoryEvents_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma mergeLoTraced_memoryEvents_empty
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {ssa ssb : Int}
  {na nb : Nat} :
-- imply
  (mergeLoTraced? state ssa ssb na nb).trace.memoryEvents = [] :=
-- proof
  (mergeLoTraced_topLevelEvents_empty state ssa ssb na nb).1

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoTraced_policyEvents_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma mergeLoTraced_policyEvents_empty
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {ssa ssb : Int}
  {na nb : Nat} :
-- imply
  (mergeLoTraced? state ssa ssb na nb).trace.policyEvents = [] :=
-- proof
  (mergeLoTraced_topLevelEvents_empty state ssa ssb na nb).2

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeLoFuelFailureTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma erase_mergeLoFuelFailureTraced
  {κ : Type u}
  {ν : Type v}
  {machine : MergeLoMachine κ ν} :
-- imply
  (mergeLoFuelFailureTraced machine).erase = mergeLoGallopFuelFailure machine := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeLoCopyAIncrTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma erase_mergeLoCopyAIncrTraced
  {κ : Type u}
  {ν : Type v}
  {machine : MergeLoMachine κ ν} :
-- imply
  (mergeLoCopyAIncrTraced? machine).erase = mergeLoCopyAIncr? machine := by
-- proof
  rw [mergeLoCopyAIncrTraced?, TraceResult.erase_map,
    erase_tempToMainCellTraced]
  unfold tempToMainCell? mergeLoCopyAIncr?
  rw [mergeTempRead_ofNat]
  cases hread : mergeLoTempRead? machine.state.a machine.aPos with
  | none => simp
  | some entry =>
    cases hwrite : machine.state.data.write? machine.dest entry <;>
      simp [hwrite]

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeLoCopyBIncrTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma erase_mergeLoCopyBIncrTraced
  {κ : Type u}
  {ν : Type v}
  {machine : MergeLoMachine κ ν} :
-- imply
  (mergeLoCopyBIncrTraced? machine).erase = mergeLoCopyBIncr? machine := by
-- proof
  rw [mergeLoCopyBIncrTraced?, TraceResult.erase_map,
    erase_mainDataMemmoveTraced]
  unfold mainDataMemmove? SortSlice.memmove? mergeLoCopyBIncr?
  split <;>
    simp [SortSlice.memmoveForward?, SortSlice.memmoveBackward?,
      SortSlice.copy?, SortSlice.copyFrom?, Option.bind_assoc]

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeLoSucceedTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma erase_mergeLoSucceedTraced
  {κ : Type u}
  {ν : Type v}
  {machine : MergeLoMachine κ ν} :
-- imply
  (mergeLoSucceedTraced? machine).erase = mergeLoSucceed? machine := by
-- proof
  rw [mergeLoSucceedTraced?, TraceResult.erase_map,
    erase_tempToMainMemcpyTraced,
    tempToMainMemcpy_eq_mergeLo .finalTempToData rfl]
  cases hcopy : mergeLoMemcpyTempToData? .finalTempToData rfl machine.na
    machine.state machine.dest machine.aPos <;>
    simp [mergeLoSucceed?, hcopy]

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeLoCopyBTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma erase_mergeLoCopyBTraced
  {κ : Type u}
  {ν : Type v}
  {machine : MergeLoMachine κ ν} :
-- imply
  (mergeLoCopyBTraced? machine).erase = mergeLoCopyB? machine := by
-- proof
  unfold mergeLoCopyBTraced? mergeLoCopyB?
  simp only [mergeDataMemmove_eq]
  split
  · rw [TraceResult.erase_bind, erase_mainDataMemmoveTraced]
    unfold mainDataMemmove?
    cases hmove : machine.state.data.memmove? machine.dest machine.bPos
      machine.nb with
    | none => simp
    | some data =>
      simp only [bind, Option.bind, pure]
      rw [TraceResult.erase_map, erase_tempToMainCellTraced]
      unfold tempToMainCell?
      rw [mergeTempRead_ofNat]
      cases hread : mergeLoTempRead? machine.state.a machine.aPos with
      | none => simp
      | some entry =>
        simp only [bind, Option.bind, pure]
        cases hwrite : data.write?
          (machine.dest + Int.ofNat machine.nb) entry with
        | none => rfl
        | some updated => rfl
  · rfl

end CPythonListsort

namespace CPythonListsort.MergeLoStableFrame

/--
[refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma refl
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν} :
-- imply
  MergeLoStableFrame state state := by
-- proof
  constructor <;> rfl

end CPythonListsort.MergeLoStableFrame

namespace CPythonListsort.MergeLoStableFrame

/--
[trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma trans
  {κ : Type u}
  {ν : Type v}
  {first second third : MergeState κ ν}
-- given
  (hfirst : MergeLoStableFrame first second)
  (hsecond : MergeLoStableFrame second third) :
-- imply
  MergeLoStableFrame first third := by
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

end CPythonListsort.MergeLoStableFrame

namespace CPythonListsort.MergeLoStableFrame

/--
[of_movement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma of_movement
  {κ : Type u}
  {ν : Type v}
  {before after : MergeState κ ν}
-- given
  (hframe : MergeMovementFrame before after) :
-- imply
  MergeLoStableFrame before after := by
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

end CPythonListsort.MergeLoStableFrame

namespace CPythonListsort.MergeLoStableFrame

/--
[of_getmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma of_getmem
  {κ : Type u}
  {ν : Type v}
  {before : MergeState κ ν}
  {need : PySSize}
  {post : MergeGetmemStoragePost before need (mergeGetmem before need)} :
-- imply
  MergeLoStableFrame before (mergeGetmem before need).state := by
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

end CPythonListsort.MergeLoStableFrame

namespace CPythonListsort.MergeLoStorageFrame

/--
[refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma refl
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν} :
-- imply
  MergeLoStorageFrame state state := by
-- proof
  constructor <;> rfl

end CPythonListsort.MergeLoStorageFrame

namespace CPythonListsort.MergeLoStorageFrame

/--
[trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma trans
  {κ : Type u}
  {ν : Type v}
  {first second third : MergeState κ ν}
-- given
  (hfirst : MergeLoStorageFrame first second)
  (hsecond : MergeLoStorageFrame second third) :
-- imply
  MergeLoStorageFrame first third := by
-- proof
  exact
    { cellsSize := hsecond.cellsSize.trans hfirst.cellsSize
      backing := hsecond.backing.trans hfirst.backing
      hasValues := hsecond.hasValues.trans hfirst.hasValues
      alloced := hsecond.alloced.trans hfirst.alloced }

end CPythonListsort.MergeLoStorageFrame

namespace CPythonListsort.MergeLoStorageFrame

/--
[of_movement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma of_movement
  {κ : Type u}
  {ν : Type v}
  {before after : MergeState κ ν}
-- given
  (hframe : MergeMovementFrame before after) :
-- imply
  MergeLoStorageFrame before after :=
-- proof
  { cellsSize := hframe.tempSize
    backing := hframe.tempBacking
    hasValues := hframe.tempValuesMode
    alloced := hframe.alloced }

end CPythonListsort.MergeLoStorageFrame

namespace CPythonListsort.MergeLoStorageFrame

/--
[physicalSlots_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma physicalSlots_eq
  {κ : Type u}
  {ν : Type v}
  {before after : MergeState κ ν}
-- given
  (hframe : MergeLoStorageFrame before after) :
-- imply
  after.a.physicalSlots = before.a.physicalSlots := by
-- proof
  simp only [TempStorage.physicalSlots, TempStorage.multiplier]
  rw [hframe.cellsSize, hframe.hasValues]

end CPythonListsort.MergeLoStorageFrame

namespace CPythonListsort.MergeLoMachineInvariant

/--
[aPosInBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma aPosInBounds
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
-- given
  (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hna : 0 < machine.na) :
-- imply
  TempIndexInBounds machine.state.a (Int.ofNat machine.aPos) := by
-- proof
  constructor
  · exact Int.natCast_nonneg _
  · apply Int.ofNat_lt.mpr
    have haccounting := h.tempAccounting
    have hcapacity := h.tempCapacity
    omega

end CPythonListsort.MergeLoMachineInvariant

namespace CPythonListsort.MergeLoMachineInvariant

/--
[tempReadable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma tempReadable
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
-- given
  (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hna : 0 < machine.na) :
-- imply
  ∃ entry, mergeTempRead? machine.state.a (Int.ofNat machine.aPos) = some entry := by
-- proof
  have haPos : machine.aPos < tempTotal := by
    have haccounting := h.tempAccounting
    omega
  obtain ⟨entry, hread, _⟩ := h.tempValuesMode machine.aPos haPos
  refine ⟨entry, ?_⟩
  rw [erase_mergeTempRead] at hread
  simpa only [zero_add] using hread

end CPythonListsort.MergeLoMachineInvariant

namespace CPythonListsort.MergeLoMachineInvariant

/--
[tempActiveInBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma tempActiveInBounds
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
-- given
  (h : MergeLoMachineInvariant origin tempTotal endIndex machine) :
-- imply
  TempRangeInBounds machine.state.a (Int.ofNat machine.aPos) machine.na := by
-- proof
  constructor
  · exact Int.natCast_nonneg _
  · have hbound : machine.aPos + machine.na ≤
    machine.state.a.cells.size := by
    have haccounting := h.tempAccounting
    have hcapacity := h.tempCapacity
    omega
    simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using Int.ofNat_le.mpr hbound

end CPythonListsort.MergeLoMachineInvariant

namespace CPythonListsort.MergeLoMachineInvariant

/--
[tempActiveValuesMode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma tempActiveValuesMode
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
-- given
  (h : MergeLoMachineInvariant origin tempTotal endIndex machine) :
-- imply
  TempRangeValuesMode machine.state.a (Int.ofNat machine.aPos) machine.na := by
-- proof
  intro offset hoffset
  have hfull : machine.aPos + offset < tempTotal := by
    have haccounting := h.tempAccounting
    omega
  rcases h.tempValuesMode (machine.aPos + offset) hfull with
    ⟨entry, hread, hentryMode⟩
  refine ⟨entry, ?_, hentryMode⟩
  simpa only [zero_add, Int.ofNat_eq_natCast, Nat.cast_add] using hread

end CPythonListsort.MergeLoMachineInvariant

namespace CPythonListsort.MergeLoMachineInvariant

/--
[temporaryValidRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma temporaryValidRange
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
-- given
  (h : MergeLoMachineInvariant origin tempTotal endIndex machine) :
-- imply
  (GallopKeySource.temporary machine.state.a (Int.ofNat machine.aPos)).ValidRange machine.na :=
-- proof
  mergeLoTemporary_validRange machine.state.a machine.aPos machine.na
    (by
      have haccounting := h.tempAccounting
      have hcapacity := h.tempCapacity
      omega) (by
      intro i hi
      obtain ⟨entry, hread, _⟩ := h.tempActiveValuesMode i hi
      refine ⟨entry, ?_⟩
      rw [erase_mergeTempRead] at hread
      have hsum : Int.ofNat machine.aPos + Int.ofNat i =
        Int.ofNat (machine.aPos + i) := by
        simp only [Int.ofNat_eq_natCast, Nat.cast_add]
      rw [hsum, mergeTempRead_ofNat] at hread
      exact hread)

end CPythonListsort.MergeLoMachineInvariant

namespace CPythonListsort.MergeLoMachineInvariant

/--
[bPosInBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma bPosInBounds
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
-- given
  (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hnb : 0 < machine.nb) :
-- imply
  SortSlice.IndexInBounds machine.state.data machine.bPos := by
-- proof
  have hadjacent := h.adjacency
  have hdest := h.destNonnegative
  have hright := h.rightAccounting
  have hend := h.mainEnd
  rw [SortSlice.IndexInBounds]
  simp only [Int.ofNat_eq_natCast] at hadjacent hright hend ⊢
  constructor <;> omega

end CPythonListsort.MergeLoMachineInvariant

namespace CPythonListsort.MergeLoMachineInvariant

/--
[destInBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma destInBounds
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
-- given
  (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hactive : 0 < machine.na + machine.nb) :
-- imply
  SortSlice.IndexInBounds machine.state.data machine.dest := by
-- proof
  have hadjacent := h.adjacency
  have hright := h.rightAccounting
  have hend := h.mainEnd
  rw [SortSlice.IndexInBounds]
  simp only [Int.ofNat_eq_natCast] at hadjacent hright hend ⊢
  constructor
  · exact h.destNonnegative
  · omega

end CPythonListsort.MergeLoMachineInvariant

namespace CPythonListsort.MergeLoMachineInvariant

/--
[rightValidRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma rightValidRange
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
-- given
  (h : MergeLoMachineInvariant origin tempTotal endIndex machine) :
-- imply
  (GallopKeySource.main machine.state.data machine.bPos).ValidRange machine.nb := by
-- proof
  have hadjacent := h.adjacency
  have hright := h.rightAccounting
  have hend := h.mainEnd
  have hdest := h.destNonnegative
  simp only [Int.ofNat_eq_natCast] at hadjacent hright hend
  refine ⟨by
    simp only [GallopKeySource.base]
    omega, ?_, ?_⟩
  · simp only [GallopKeySource.base, GallopKeySource.extent]
    exact hright.trans_le hend
  · intro offset hoffset
    have hindex : SortSlice.IndexInBounds machine.state.data
      (machine.bPos + Int.ofNat offset) := by
      rw [SortSlice.IndexInBounds]
      constructor
      · exact add_nonneg (by omega) (Int.natCast_nonneg _)
      · calc
        machine.bPos + Int.ofNat offset <
          machine.bPos + Int.ofNat machine.nb := by
            simpa [add_comm] using
              (add_lt_add_left (Int.ofNat_lt.mpr hoffset) machine.bPos)
        _ = endIndex := h.rightAccounting
        _ ≤ Int.ofNat machine.state.data.entries.size := h.mainEnd
    rcases SortSlice.read_eq_some_of_indexInBounds machine.state.data _ hindex with
      ⟨entry, hentry⟩
    exact ⟨entry, by
      simpa only [GallopKeySource.read?, GallopKeySource.base] using hentry⟩

end CPythonListsort.MergeLoMachineInvariant

namespace CPythonListsort.MergeLoMachineInvariant

/--
[destRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma destRange
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
  {count : Nat}
-- given
  (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hcount : count ≤ machine.na) :
-- imply
  SortSlice.RangeInBounds machine.state.data machine.dest count := by
-- proof
  constructor
  · exact h.destNonnegative
  · have hadj := h.adjacency
    have hright := h.rightAccounting
    have hend := h.mainEnd
    simp only [Int.ofNat_eq_natCast] at hadj hright hend ⊢
    have hcast : (count : Int) ≤ (machine.na : Int) := by exact_mod_cast hcount
    omega

end CPythonListsort.MergeLoMachineInvariant

namespace CPythonListsort.MergeLoMachineInvariant

/--
[destTotalRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma destTotalRange
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
  {count : Nat}
-- given
  (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hcount : count ≤ machine.na + machine.nb) :
-- imply
  SortSlice.RangeInBounds machine.state.data machine.dest count := by
-- proof
  constructor
  · exact h.destNonnegative
  · have hadj := h.adjacency
    have hright := h.rightAccounting
    have hend := h.mainEnd
    simp only [Int.ofNat_eq_natCast] at hadj hright hend ⊢
    have hcast : (count : Int) ≤ (machine.na + machine.nb : Nat) := by
      exact_mod_cast hcount
    omega

end CPythonListsort.MergeLoMachineInvariant

namespace CPythonListsort.MergeLoMachineInvariant

/--
[rightRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma rightRange
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
  {count : Nat}
-- given
  (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hcount : count ≤ machine.nb) :
-- imply
  SortSlice.RangeInBounds machine.state.data machine.bPos count := by
-- proof
  constructor
  · have hadj := h.adjacency
    simp only [Int.ofNat_eq_natCast] at hadj
    exact hadj ▸ add_nonneg h.destNonnegative (Int.natCast_nonneg _)
  · have hright := h.rightAccounting
    have hend := h.mainEnd
    simp only [Int.ofNat_eq_natCast] at hright hend ⊢
    have hcast : (count : Int) ≤ (machine.nb : Int) := by exact_mod_cast hcount
    omega

end CPythonListsort.MergeLoMachineInvariant

namespace CPythonListsort.MergeLoMachineInvariant

/--
[tempPrefixInBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma tempPrefixInBounds
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
  {count : Nat}
-- given
  (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hcount : count ≤ machine.na) :
-- imply
  TempRangeInBounds machine.state.a (Int.ofNat machine.aPos) count := by
-- proof
  constructor
  · exact Int.natCast_nonneg _
  · have haccount := h.tempAccounting
    have hcapacity := h.tempCapacity
    simp only [Int.ofNat_eq_natCast] at ⊢
    have hcast : (count : Int) ≤ (machine.na : Int) := by exact_mod_cast hcount
    exact_mod_cast (show machine.aPos + count ≤ machine.state.a.cells.size by
      omega)

end CPythonListsort.MergeLoMachineInvariant

namespace CPythonListsort.MergeLoMachineInvariant

/--
[tempPrefixValuesMode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma tempPrefixValuesMode
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
  {count : Nat}
-- given
  (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hcount : count ≤ machine.na) :
-- imply
  TempRangeValuesMode machine.state.a (Int.ofNat machine.aPos) count := by
-- proof
  intro offset hoffset
  exact h.tempActiveValuesMode offset (by omega)

end CPythonListsort.MergeLoMachineInvariant

namespace CPythonListsort.MergeLoMachineInvariant

/--
[replaceState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma replaceState
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
  {after : MergeState κ ν}
-- given
  (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hframe : MergeMovementFrame machine.state after)
  (htemp : after.a = machine.state.a)
  (hmode : SortSlice.ValuesModeInvariant after.a.hasValues after.data) :
-- imply
  MergeLoMachineInvariant origin tempTotal endIndex { machine with state := after } := by
-- proof
  exact
    { destNonnegative := h.destNonnegative
      tempAccounting := h.tempAccounting
      adjacency := h.adjacency
      rightAccounting := h.rightAccounting
      mainEnd := by simpa only [hframe.dataSize] using h.mainEnd
      leftWordBound := h.leftWordBound
      rightWordBound := h.rightWordBound
      tempCapacity := by simpa only [htemp] using h.tempCapacity
      tempValuesMode := by simpa only [htemp] using h.tempValuesMode
      tempInvariant := hframe.tempStorageInv h.tempInvariant
      tempLive := hframe.live h.tempLive
      valuesMode := hmode
      stableFrame := h.stableFrame.trans (.of_movement hframe)
      storageFrame := h.storageFrame.trans (.of_movement hframe) }

end CPythonListsort.MergeLoMachineInvariant

namespace CPythonListsort.MergeLoMachineInvariant

/--
[setMinGallop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma setMinGallop
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
  {minGallop : PySSize}
-- given
  (h : MergeLoMachineInvariant origin tempTotal endIndex machine) :
-- imply
  MergeLoMachineInvariant origin tempTotal endIndex { machine with state := { machine.state with min_gallop := minGallop } minGallop := minGallop } := by
-- proof
  exact
    { destNonnegative := h.destNonnegative
      tempAccounting := h.tempAccounting
      adjacency := h.adjacency
      rightAccounting := h.rightAccounting
      mainEnd := h.mainEnd
      leftWordBound := h.leftWordBound
      rightWordBound := h.rightWordBound
      tempCapacity := h.tempCapacity
      tempValuesMode := h.tempValuesMode
      tempInvariant := h.tempInvariant
      tempLive := h.tempLive
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

end CPythonListsort.MergeLoMachineInvariant

namespace CPythonListsort.MergeLoMachineInvariant

/--
[setMachineMinGallop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma setMachineMinGallop
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
  {minGallop : PySSize}
-- given
  (h : MergeLoMachineInvariant origin tempTotal endIndex machine) :
-- imply
  MergeLoMachineInvariant origin tempTotal endIndex { machine with minGallop := minGallop } := by
-- proof
  exact
    { destNonnegative := h.destNonnegative
      tempAccounting := h.tempAccounting
      adjacency := h.adjacency
      rightAccounting := h.rightAccounting
      mainEnd := h.mainEnd
      leftWordBound := h.leftWordBound
      rightWordBound := h.rightWordBound
      tempCapacity := h.tempCapacity
      tempValuesMode := h.tempValuesMode
      tempInvariant := h.tempInvariant
      tempLive := h.tempLive
      valuesMode := h.valuesMode
      stableFrame := h.stableFrame
      storageFrame := h.storageFrame }

end CPythonListsort.MergeLoMachineInvariant

namespace CPythonListsort.MergeLoMachineInvariant

/--
[copyA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma copyA
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
  {after : MergeState κ ν}
-- given
  (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hframe : MergeMovementFrame machine.state after)
  (htemp : after.a = machine.state.a)
  (hmode : SortSlice.ValuesModeInvariant after.a.hasValues after.data)
  (hna : 0 < machine.na) :
-- imply
  MergeLoMachineInvariant origin tempTotal endIndex { machine with state := after dest := machine.dest + 1 aPos := machine.aPos + 1 na := machine.na - 1 } := by
-- proof
  have hs := h.replaceState after hframe htemp hmode
  exact
    { destNonnegative := by
      change 0 ≤ machine.dest + 1
      exact add_nonneg h.destNonnegative (by omega)
      tempAccounting := by
        change machine.aPos + 1 + (machine.na - 1) = tempTotal
        have := h.tempAccounting
        omega
      adjacency := by
        have hadjacent := h.adjacency
        simp only [Int.ofNat_eq_natCast, Nat.cast_sub hna] at hadjacent ⊢
        omega
      rightAccounting := h.rightAccounting
      mainEnd := hs.mainEnd
      leftWordBound := by
        change machine.na - 1 ≤ PY_LIST_MAX
        exact (Nat.sub_le machine.na 1).trans h.leftWordBound
      rightWordBound := h.rightWordBound
      tempCapacity := hs.tempCapacity
      tempValuesMode := hs.tempValuesMode
      tempInvariant := hs.tempInvariant
      tempLive := hs.tempLive
      valuesMode := hs.valuesMode
      stableFrame := hs.stableFrame
      storageFrame := hs.storageFrame }

end CPythonListsort.MergeLoMachineInvariant

namespace CPythonListsort.MergeLoMachineInvariant

/--
[copyB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma copyB
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
  {after : MergeState κ ν}
-- given
  (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hframe : MergeMovementFrame machine.state after)
  (htemp : after.a = machine.state.a)
  (hmode : SortSlice.ValuesModeInvariant after.a.hasValues after.data)
  (hnb : 0 < machine.nb) :
-- imply
  MergeLoMachineInvariant origin tempTotal endIndex { machine with state := after dest := machine.dest + 1 bPos := machine.bPos + 1 nb := machine.nb - 1 } := by
-- proof
  have hs := h.replaceState after hframe htemp hmode
  exact
    { destNonnegative := by
      change 0 ≤ machine.dest + 1
      exact add_nonneg h.destNonnegative (by omega)
      tempAccounting := h.tempAccounting
      adjacency := by
        have hadjacent := h.adjacency
        simp only [Int.ofNat_eq_natCast] at hadjacent ⊢
        omega
      rightAccounting := by
        have hright := h.rightAccounting
        simp only [Int.ofNat_eq_natCast, Nat.cast_sub hnb] at hright ⊢
        omega
      mainEnd := hs.mainEnd
      leftWordBound := h.leftWordBound
      rightWordBound := by
        change machine.nb - 1 ≤ PY_LIST_MAX
        exact (Nat.sub_le machine.nb 1).trans h.rightWordBound
      tempCapacity := hs.tempCapacity
      tempValuesMode := hs.tempValuesMode
      tempInvariant := hs.tempInvariant
      tempLive := hs.tempLive
      valuesMode := hs.valuesMode
      stableFrame := hs.stableFrame
      storageFrame := hs.storageFrame }

end CPythonListsort.MergeLoMachineInvariant

namespace CPythonListsort.MergeLoMachineInvariant

/--
[copyABlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma copyABlock
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
  {count : Nat}
  {after : MergeState κ ν}
-- given
  (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hcount : count ≤ machine.na)
  (hframe : MergeMovementFrame machine.state after)
  (htemp : after.a = machine.state.a)
  (hmode : SortSlice.ValuesModeInvariant after.a.hasValues after.data) :
-- imply
  MergeLoMachineInvariant origin tempTotal endIndex { machine with state := after dest := machine.dest + Int.ofNat count aPos := machine.aPos + count na := machine.na - count } := by
-- proof
  have hs := h.replaceState after hframe htemp hmode
  exact
    { destNonnegative := add_nonneg h.destNonnegative (Int.natCast_nonneg _)
      tempAccounting := by
        change machine.aPos + count + (machine.na - count) = tempTotal
        have := h.tempAccounting
        omega
      adjacency := by
        have hadjacent := h.adjacency
        simp only [Int.ofNat_eq_natCast, Nat.cast_sub hcount]
          at hadjacent ⊢
        omega
      rightAccounting := h.rightAccounting
      mainEnd := hs.mainEnd
      leftWordBound := by
        change machine.na - count ≤ PY_LIST_MAX
        exact (Nat.sub_le machine.na count).trans h.leftWordBound
      rightWordBound := h.rightWordBound
      tempCapacity := hs.tempCapacity
      tempValuesMode := hs.tempValuesMode
      tempInvariant := hs.tempInvariant
      tempLive := hs.tempLive
      valuesMode := hs.valuesMode
      stableFrame := hs.stableFrame
      storageFrame := hs.storageFrame }

end CPythonListsort.MergeLoMachineInvariant

namespace CPythonListsort.MergeLoMachineInvariant

/--
[copyBBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma copyBBlock
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
  {count : Nat}
  {after : MergeState κ ν}
-- given
  (h : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hcount : count ≤ machine.nb)
  (hframe : MergeMovementFrame machine.state after)
  (htemp : after.a = machine.state.a)
  (hmode : SortSlice.ValuesModeInvariant after.a.hasValues after.data) :
-- imply
  MergeLoMachineInvariant origin tempTotal endIndex { machine with state := after dest := machine.dest + Int.ofNat count bPos := machine.bPos + Int.ofNat count nb := machine.nb - count } := by
-- proof
  have hs := h.replaceState after hframe htemp hmode
  exact
    { destNonnegative := add_nonneg h.destNonnegative (Int.natCast_nonneg _)
      tempAccounting := h.tempAccounting
      adjacency := by
        have hadjacent := h.adjacency
        simp only [Int.ofNat_eq_natCast] at hadjacent ⊢
        omega
      rightAccounting := by
        have hright := h.rightAccounting
        simp only [Int.ofNat_eq_natCast, Nat.cast_sub hcount] at hright ⊢
        omega
      mainEnd := hs.mainEnd
      leftWordBound := h.leftWordBound
      rightWordBound := by
        change machine.nb - count ≤ PY_LIST_MAX
        exact (Nat.sub_le machine.nb count).trans h.rightWordBound
      tempCapacity := hs.tempCapacity
      tempValuesMode := hs.tempValuesMode
      tempInvariant := hs.tempInvariant
      tempLive := hs.tempLive
      valuesMode := hs.valuesMode
      stableFrame := hs.stableFrame
      storageFrame := hs.storageFrame }

end CPythonListsort.MergeLoMachineInvariant

namespace CPythonListsort

/--
[mergeLoNaZeroHedgeRegressionMachine_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma mergeLoNaZeroHedgeRegressionMachine_invariant
  {κ : Type u}
  {ν : Type v} :
-- imply
  MergeLoMachineInvariant mergeLoNaZeroHedgeRegressionState 2 3 mergeLoNaZeroHedgeRegressionMachine := by
-- proof
  refine
    { destNonnegative := by decide
      tempAccounting := by decide
      adjacency := by decide
      rightAccounting := by decide
      mainEnd := by decide
      leftWordBound := by decide
      rightWordBound := by decide
      tempCapacity := by decide
      tempValuesMode := ?_
      tempInvariant := by
        have hcapacity : 4 ≤ MERGESTATE_TEMP_SIZE := by decide
        simpa [mergeLoNaZeroHedgeRegressionMachine,
          mergeLoNaZeroHedgeRegressionState, TempStorageInv,
          TempStorage.multiplier] using hcapacity
      tempLive := by
        simp [mergeLoNaZeroHedgeRegressionMachine,
          mergeLoNaZeroHedgeRegressionState, TempStorage.Live]
      valuesMode := ?_
      stableFrame := ?_
      storageFrame := ?_ }
  · intro index hindex
    have hindex' : index < 2 := by
      simpa [mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · intro index hindex
    have hindex' : index < 3 := by
      simpa [mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · simpa [mergeLoNaZeroHedgeRegressionMachine] using
    MergeLoStableFrame.refl mergeLoNaZeroHedgeRegressionState
  · simpa [mergeLoNaZeroHedgeRegressionMachine] using
    MergeLoStorageFrame.refl mergeLoNaZeroHedgeRegressionState

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoNaZeroHedgeStrictControlMachine_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma mergeLoNaZeroHedgeStrictControlMachine_invariant
  {κ : Type u}
  {ν : Type v} :
-- imply
  MergeLoMachineInvariant mergeLoNaZeroHedgeStrictControlState 2 3 mergeLoNaZeroHedgeStrictControlMachine := by
-- proof
  refine
    { destNonnegative := by decide
      tempAccounting := by decide
      adjacency := by decide
      rightAccounting := by decide
      mainEnd := by decide
      leftWordBound := by decide
      rightWordBound := by decide
      tempCapacity := by decide
      tempValuesMode := ?_
      tempInvariant := by
        have hcapacity : 4 ≤ MERGESTATE_TEMP_SIZE := by decide
        simpa [mergeLoNaZeroHedgeStrictControlMachine,
          mergeLoNaZeroHedgeStrictControlState,
          mergeLoNaZeroHedgeRegressionMachine,
          mergeLoNaZeroHedgeRegressionState, TempStorageInv,
          TempStorage.multiplier] using hcapacity
      tempLive := by
        simp [mergeLoNaZeroHedgeStrictControlMachine,
          mergeLoNaZeroHedgeStrictControlState,
          mergeLoNaZeroHedgeRegressionMachine,
          mergeLoNaZeroHedgeRegressionState, TempStorage.Live]
      valuesMode := ?_
      stableFrame := ?_
      storageFrame := ?_ }
  · intro index hindex
    have hindex' : index < 2 := by
      simpa [mergeLoNaZeroHedgeStrictControlMachine,
        mergeLoNaZeroHedgeStrictControlState,
        mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeLoNaZeroHedgeStrictControlMachine,
        mergeLoNaZeroHedgeStrictControlState,
        mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · intro index hindex
    have hindex' : index < 3 := by
      simpa [mergeLoNaZeroHedgeStrictControlMachine,
        mergeLoNaZeroHedgeStrictControlState,
        mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState] using hindex
    interval_cases index <;>
      simp [mergeLoNaZeroHedgeStrictControlMachine,
        mergeLoNaZeroHedgeStrictControlState,
        mergeLoNaZeroHedgeRegressionMachine,
        mergeLoNaZeroHedgeRegressionState,
        SortSlice.EntryMatchesValuesMode]
  · simpa [mergeLoNaZeroHedgeStrictControlMachine] using
    MergeLoStableFrame.refl mergeLoNaZeroHedgeStrictControlState
  · simpa [mergeLoNaZeroHedgeStrictControlMachine] using
    MergeLoStorageFrame.refl mergeLoNaZeroHedgeStrictControlState

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mainDataMemmoveTraced_temp_eq_of_result](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mainDataMemmoveTraced_temp_eq_of_result
  (state result : MergeState κ ν) (dst src : Int) (count : Nat)
  (hresult : (mainDataMemmoveTraced? state dst src count).result =
    some result) :
  result.a = state.a := by
  unfold mainDataMemmoveTraced? at hresult
  cases hdata : (SortSlice.memmoveTraced? state.a.hasValues state.data dst src
    count).result with
  | none => simp [TraceResult.map, hdata] at hresult
  | some data =>
    simp [TraceResult.map, hdata] at hresult
    subst result
    rfl

end CPythonListsort

namespace CPythonListsort.MergeLoCorePost

variable {κ : Type u} {ν : Type v}
/--
[reference_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma reference_eq
  (origin : MergeState κ ν) (tempTotal : Nat)
  (execution : TraceResult (MergeLoResult κ ν))
  (first second : Option (MergeLoResult κ ν))
  (result : MergeLoResult κ ν) (heq : first = second)
  (h : MergeLoCorePost origin tempTotal execution first result) :
  MergeLoCorePost origin tempTotal execution second result := by
  subst second
  exact h

end CPythonListsort.MergeLoCorePost

namespace CPythonListsort.MergeLoCorePost

variable {κ : Type u} {ν : Type v}
/--
[prepend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
continuation.  The reference computation is prefixed by the erased primitive
in exactly the same way. -/
private lemma prepend
  (origin : MergeState κ ν) (tempTotal : Nat)
  (current : TraceResult α) (next : α → TraceResult (MergeLoResult κ ν))
  (reference : α → Option (MergeLoResult κ ν))
  (value : α) (result : MergeLoResult κ ν)
  (hcurrent : current.result = some value)
  (hcurrentSafe : MovementTraceSafe current)
  (hnext : MergeLoCorePost origin tempTotal (next value)
    (reference value) result) :
  MergeLoCorePost origin tempTotal (current.bind next)
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
        rwa [TraceResult.erase_bind, herase]
      tempCapacity := hnext.tempCapacity
      tempInvariant := hnext.tempInvariant
      tempLive := hnext.tempLive
      valuesMode := hnext.valuesMode
      stableFrame := hnext.stableFrame
      storageFrame := hnext.storageFrame }

end CPythonListsort.MergeLoCorePost

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoTempReadTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoTempReadTraced_safe (storage : TempStorage κ ν)
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
[mergeLoMainKeyReadTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoMainKeyReadTraced_safe (slice : SortSlice κ ν)
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

/--
[mergeLoCopyBIncrTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma mergeLoCopyBIncrTraced_safe
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
-- given
  (hinvariant : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hna : 0 < machine.na)
  (hnb : 0 < machine.nb) :
-- imply
  ∃ next, (mergeLoCopyBIncrTraced? machine).result = some next ∧ MovementTraceSafe (mergeLoCopyBIncrTraced? machine) ∧ MergeLoMachineInvariant origin tempTotal endIndex next ∧ next.na = machine.na ∧ next.nb = machine.nb - 1 := by
-- proof
  have hdestIndex := hinvariant.destInBounds (by omega)
  have hsourceIndex := hinvariant.bPosInBounds hnb
  have hdest : SortSlice.RangeInBounds machine.state.data machine.dest 1 := by
    rw [SortSlice.IndexInBounds] at hdestIndex
    simp only [Int.ofNat_eq_natCast] at hdestIndex ⊢
    constructor
    · exact hdestIndex.1
    · have hle : machine.dest + 1 ≤
      (machine.state.data.entries.size : Int) := by omega
      simpa [Int.ofNat_eq_natCast] using hle
  have hsource : SortSlice.RangeInBounds machine.state.data machine.bPos 1 := by
    rw [SortSlice.IndexInBounds] at hsourceIndex
    simp only [Int.ofNat_eq_natCast] at hsourceIndex ⊢
    constructor
    · exact hsourceIndex.1
    · have hle : machine.bPos + 1 ≤
      (machine.state.data.entries.size : Int) := by omega
      simpa [Int.ofNat_eq_natCast] using hle
  rcases mainDataMemmoveTraced_safe machine.state machine.dest machine.bPos 1
    hinvariant.tempInvariant hinvariant.tempLive hinvariant.valuesMode
    hdest hsource with ⟨state, hpost⟩
  let next : MergeLoMachine κ ν :=
    { machine with
      state := state
      dest := machine.dest + 1
      bPos := machine.bPos + 1
      nb := machine.nb - 1 }
  have htempEq := mainDataMemmoveTraced_temp_eq_of_result machine.state state
    machine.dest machine.bPos 1 hpost.success
  have hnextInv : MergeLoMachineInvariant origin tempTotal endIndex next := by
    exact hinvariant.copyB state hpost.frame htempEq hpost.valuesMode hnb
  refine ⟨next, ?_, ?_, hnextInv, rfl, rfl⟩
  · simp [mergeLoCopyBIncrTraced?, TraceResult.map, hpost.success, next]
  · exact MovementTraceSafe.map _ _ hpost.traceSafe

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoCopyAIncrTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma mergeLoCopyAIncrTraced_safe
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
-- given
  (hinvariant : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hna : 0 < machine.na) :
-- imply
  ∃ next, (mergeLoCopyAIncrTraced? machine).result = some next ∧ MovementTraceSafe (mergeLoCopyAIncrTraced? machine) ∧ MergeLoMachineInvariant origin tempTotal endIndex next ∧ next.na = machine.na - 1 ∧ next.nb = machine.nb := by
-- proof
  have hdest := hinvariant.destInBounds (by omega)
  have htemp := hinvariant.aPosInBounds hna
  have hreadable := hinvariant.tempReadable hna
  rcases tempToMainCellTraced_safe machine.state machine.dest
    (Int.ofNat machine.aPos) hdest htemp hinvariant.tempLive hreadable with
    ⟨state, hstate, htraceSafe, hframe⟩
  have hcore : tempToMainCell? machine.state machine.dest
    (Int.ofNat machine.aPos) = some state := by
    rwa [← erase_tempToMainCellTraced]
  have htempEq := tempToMainCell_temp_eq_of_eq_some machine.state state
    machine.dest (Int.ofNat machine.aPos) hcore
  have hentryMode : ∀ entry,
    mergeTempRead? machine.state.a (Int.ofNat machine.aPos) = some entry →
      SortSlice.EntryMatchesValuesMode machine.state.a.hasValues entry := by
    intro entry hentry
    have haPos : machine.aPos < tempTotal := by
      have := hinvariant.tempAccounting
      omega
    rcases hinvariant.tempValuesMode machine.aPos haPos with
      ⟨stored, hstored, hstoredMode⟩
    rw [erase_mergeTempRead] at hstored
    simp only [zero_add] at hstored
    have : stored = entry := by
      apply Option.some.inj
      exact hstored.symm.trans hentry
    simpa [this] using hstoredMode
  have hmode := tempToMainCell_valuesMode_of_eq_some machine.state state
    machine.dest (Int.ofNat machine.aPos) hinvariant.valuesMode hentryMode hcore
  let next : MergeLoMachine κ ν :=
    { machine with
      state := state
      dest := machine.dest + 1
      aPos := machine.aPos + 1
      na := machine.na - 1 }
  have hnextInv : MergeLoMachineInvariant origin tempTotal endIndex next := by
    exact hinvariant.copyA state hframe htempEq hmode hna
  refine ⟨next, ?_, ?_, hnextInv, rfl, rfl⟩
  · simp only [mergeLoCopyAIncrTraced?, TraceResult.map]
    rw [hstate]
    rfl
  · exact MovementTraceSafe.map _ _ htraceSafe

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoSucceedTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma mergeLoSucceedTraced_safe
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
-- given
  (hinvariant : MergeLoMachineInvariant origin tempTotal endIndex machine) :
-- imply
  ∃ result, MergeLoCorePost origin tempTotal (mergeLoSucceedTraced? machine) (mergeLoSucceed? machine) result := by
-- proof
  have hmain : SortSlice.RangeInBounds machine.state.data machine.dest
    machine.na := by
    constructor
    · exact hinvariant.destNonnegative
    · calc
      machine.dest + Int.ofNat machine.na = machine.bPos :=
        hinvariant.adjacency
      _ ≤ machine.bPos + Int.ofNat machine.nb :=
        le_add_of_nonneg_right (Int.natCast_nonneg _)
      _ = endIndex := hinvariant.rightAccounting
      _ ≤ Int.ofNat machine.state.data.entries.size := hinvariant.mainEnd
  rcases tempToMainMemcpyTraced_post (.lo .finalTempToData)
    mergeLoFinalTempToDataPermit machine.na machine.state machine.dest
    (Int.ofNat machine.aPos) hmain hinvariant.tempActiveInBounds
    hinvariant.tempActiveValuesMode hinvariant.tempInvariant
    hinvariant.tempLive hinvariant.valuesMode with ⟨state, hpost⟩
  let result : MergeLoResult κ ν := mergeLoSuccess state
  refine ⟨result, ?_⟩
  refine
    { resultEq := ?_
      returnCode := rfl
      resultFuel := rfl
      traceSafe := MovementTraceSafe.map _ _ hpost.traceSafe
      exactErasure := erase_mergeLoSucceedTraced machine
      tempCapacity := by
        change tempTotal ≤ state.a.cells.size
        rwa [hpost.frame.tempSize]
      tempInvariant := hpost.tempInvariant
      tempLive := hpost.tempLive
      valuesMode := hpost.valuesMode
      stableFrame := hinvariant.stableFrame.trans
        (MergeLoStableFrame.of_movement hpost.frame)
      storageFrame := hinvariant.storageFrame.trans
        (MergeLoStorageFrame.of_movement hpost.frame) }
  simp only [mergeLoSucceedTraced?, TraceResult.map]
  rw [hpost.success]
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoCopyBTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma mergeLoCopyBTraced_safe
  {κ : Type u}
  {ν : Type v}
  {origin : MergeState κ ν}
  {tempTotal : Nat}
  {endIndex : Int}
  {machine : MergeLoMachine κ ν}
-- given
  (hinvariant : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hna : machine.na = 1)
  (hnb : 0 < machine.nb) :
-- imply
  ∃ result, MergeLoCorePost origin tempTotal (mergeLoCopyBTraced? machine) (mergeLoCopyB? machine) result := by
-- proof
  have hsrc : SortSlice.RangeInBounds machine.state.data machine.bPos
    machine.nb := by
    constructor
    · have := hinvariant.adjacency
      have hd := hinvariant.destNonnegative
      simp only [hna, Int.ofNat_eq_natCast] at this
      omega
    · exact hinvariant.rightAccounting.trans_le hinvariant.mainEnd
  have hdst : SortSlice.RangeInBounds machine.state.data machine.dest
    machine.nb := by
    constructor
    · exact hinvariant.destNonnegative
    · have hadj := hinvariant.adjacency
      have hright := hinvariant.rightAccounting
      have hend := hinvariant.mainEnd
      simp only [hna, Int.ofNat_eq_natCast] at hadj hright hend ⊢
      omega
  rcases mainDataMemmoveTraced_safe machine.state machine.dest machine.bPos
    machine.nb hinvariant.tempInvariant hinvariant.tempLive
    hinvariant.valuesMode hdst hsrc with ⟨moved, hmove⟩
  have hmovedTemp := mainDataMemmoveTraced_temp_eq_of_result machine.state moved
    machine.dest machine.bPos machine.nb hmove.success
  have hmovedInv := hinvariant.replaceState moved hmove.frame hmovedTemp
    hmove.valuesMode
  have hfinalIndex : SortSlice.IndexInBounds moved.data
    (machine.dest + Int.ofNat machine.nb) := by
    rw [SortSlice.IndexInBounds]
    constructor
    · exact add_nonneg hinvariant.destNonnegative (Int.natCast_nonneg _)
    · have hright := hinvariant.rightAccounting
      have hend := hinvariant.mainEnd
      have hsize := hmove.frame.dataSize
      have hadj := hinvariant.adjacency
      simp only [hna, Int.ofNat_eq_natCast] at hright hend hadj ⊢
      rw [hsize]
      omega
  have htemp := hmovedInv.aPosInBounds (by simp [hna])
  have hreadable := hmovedInv.tempReadable (by simp [hna])
  rcases tempToMainCellTraced_safe moved
    (machine.dest + Int.ofNat machine.nb) (Int.ofNat machine.aPos)
    hfinalIndex htemp hmovedInv.tempLive hreadable with
    ⟨state, hstate, hcellSafe, hcellFrame⟩
  have hcellCore : tempToMainCell? moved
    (machine.dest + Int.ofNat machine.nb) (Int.ofNat machine.aPos) =
      some state := by
    rwa [← erase_tempToMainCellTraced]
  have hentryMode : ∀ entry,
    mergeTempRead? moved.a (Int.ofNat machine.aPos) = some entry →
      SortSlice.EntryMatchesValuesMode moved.a.hasValues entry := by
    intro entry hentry
    have haPos : machine.aPos < tempTotal := by
      have := hinvariant.tempAccounting
      omega
    rcases hmovedInv.tempValuesMode machine.aPos haPos with
      ⟨stored, hstored, hstoredMode⟩
    rw [erase_mergeTempRead] at hstored
    simp only [zero_add] at hstored
    have heq : stored = entry := Option.some.inj (hstored.symm.trans hentry)
    simpa [heq] using hstoredMode
  have hmode := tempToMainCell_valuesMode_of_eq_some moved state
    (machine.dest + Int.ofNat machine.nb) (Int.ofNat machine.aPos)
    hmove.valuesMode hentryMode hcellCore
  let result : MergeLoResult κ ν := mergeLoSuccess state
  refine ⟨result, ?_⟩
  refine
    { resultEq := ?_
      returnCode := rfl
      resultFuel := rfl
      traceSafe := ?_
      exactErasure := erase_mergeLoCopyBTraced machine
      tempCapacity := by
        change tempTotal ≤ state.a.cells.size
        rwa [hcellFrame.tempSize, hmove.frame.tempSize]
      tempInvariant := hcellFrame.tempStorageInv hmove.tempInvariant
      tempLive := hcellFrame.live hmove.tempLive
      valuesMode := hmode
      stableFrame := hinvariant.stableFrame.trans
        (MergeLoStableFrame.of_movement (hmove.frame.trans hcellFrame))
      storageFrame := hinvariant.storageFrame.trans
        (MergeLoStorageFrame.of_movement (hmove.frame.trans hcellFrame)) }
  · rw [mergeLoCopyBTraced?, if_pos ⟨hna, hnb⟩]
    simp only [TraceResult.bind, TraceResult.map]
    rw [hmove.success]
    change Option.map mergeLoSuccess
      (tempToMainCellTraced? moved
        (machine.dest + Int.ofNat machine.nb)
        (Int.ofNat machine.aPos)).result = some result
    rw [hstate]
    rfl
  · rw [mergeLoCopyBTraced?, if_pos ⟨hna, hnb⟩]
    exact MovementTraceSafe.bind _ _ moved hmove.success hmove.traceSafe
      (MovementTraceSafe.map _ _ hcellSafe)

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoOrdinaryTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
contract so the galloping step can share the same structural induction. -/
private lemma mergeLoOrdinaryTraced_safe
  (origin : MergeState κ ν) (tempTotal : Nat) (endIndex : Int)
  (fuel : Nat) (machine : MergeLoMachine κ ν) (aCount bCount : Nat)
  (hinvariant : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hfuel : MergeLoFuelInvariant (fuel + 1) machine)
  (hna : 1 < machine.na) (hnb : 0 < machine.nb)
  (ih : ∀ (next : MergeLoMachine κ ν) (phase : MergeLoPhase),
    MergeLoMachineInvariant origin tempTotal endIndex next →
    MergeLoFuelInvariant fuel next → 1 < next.na → 0 < next.nb →
    ∃ result, MergeLoCorePost origin tempTotal
      (mergeLoLoopTraced? fuel next phase)
      (mergeLoLoop? fuel next phase) result) :
  ∃ result, MergeLoCorePost origin tempTotal
    (mergeLoLoopTraced? (fuel + 1) machine (.ordinary aCount bCount))
    (mergeLoLoop? (fuel + 1) machine (.ordinary aCount bCount)) result := by
  have hguard : ¬ (machine.na ≤ 1 ∨ machine.nb = 0) := by omega
  obtain ⟨firstA, hfirstA⟩ := hinvariant.tempReadable (by omega)
  have hfirstAResult :
    (TraceResult.tempPayloadRead? machine.state.a
      (Int.ofNat machine.aPos)).result = some firstA := by
    change (TraceResult.tempPayloadRead? machine.state.a
      (Int.ofNat machine.aPos)).erase = some firstA
    rwa [TraceResult.erase_tempPayloadRead]
  have hfirstASafe := mergeLoTempReadTraced_safe machine.state.a
    (Int.ofNat machine.aPos) (hinvariant.aPosInBounds (by omega))
    hinvariant.tempLive
  rcases SortSlice.read_eq_some_of_indexInBounds machine.state.data machine.bPos
    (hinvariant.bPosInBounds hnb) with ⟨firstB, hfirstB⟩
  have hfirstBResult :
    (TraceResult.sortSliceKeysRead? machine.state.data machine.bPos).result =
      some firstB := by
    change machine.state.data.read? machine.bPos = some firstB
    exact hfirstB
  have hfirstBSafe := mergeLoMainKeyReadTraced_safe machine.state.data
    machine.bPos (hinvariant.bPosInBounds hnb)
  let tracedAfterReads := fun (left right : SortSliceEntry κ ν) =>
    if iflt machine.state.key_compare right.key left.key then
      (mergeLoCopyBIncrTraced? machine).bind fun moved =>
        let count := bCount + 1
        if moved.nb = 0 then
          mergeLoSucceedTraced? moved
        else if mergeLoCountAtLeastWord count moved.minGallop then
          mergeLoLoopTraced? fuel
            { moved with minGallop := moved.minGallop + 1 } .galloping
        else
          mergeLoLoopTraced? fuel moved (.ordinary 0 count)
    else
      (mergeLoCopyAIncrTraced? machine).bind fun moved =>
        let count := aCount + 1
        if moved.na = 1 then
          mergeLoCopyBTraced? moved
        else if mergeLoCountAtLeastWord count moved.minGallop then
          mergeLoLoopTraced? fuel
            { moved with minGallop := moved.minGallop + 1 } .galloping
        else
          mergeLoLoopTraced? fuel moved (.ordinary count 0)
  let referenceAfterReads := fun (left right : SortSliceEntry κ ν) =>
    if iflt machine.state.key_compare right.key left.key then
      (mergeLoCopyBIncr? machine).bind fun moved =>
        let count := bCount + 1
        if moved.nb = 0 then
          mergeLoSucceed? moved
        else if mergeLoCountAtLeastWord count moved.minGallop then
          mergeLoLoop? fuel
            { moved with minGallop := moved.minGallop + 1 } .galloping
        else
          mergeLoLoop? fuel moved (.ordinary 0 count)
    else
      (mergeLoCopyAIncr? machine).bind fun moved =>
        let count := aCount + 1
        if moved.na = 1 then
          mergeLoCopyB? moved
        else if mergeLoCountAtLeastWord count moved.minGallop then
          mergeLoLoop? fuel
            { moved with minGallop := moved.minGallop + 1 } .galloping
        else
          mergeLoLoop? fuel moved (.ordinary count 0)
  cases hcompare : iflt machine.state.key_compare firstB.key firstA.key with
  | false =>
    have hcompare' :
      machine.state.key_compare firstB.key firstA.key = false := by
      simpa [iflt] using hcompare
    rcases mergeLoCopyAIncrTraced_safe origin tempTotal endIndex machine
      hinvariant (by omega) with
      ⟨next, hnextResult, hnextSafe, hnextInv, hnextNa, hnextNb⟩
    let nextACount := aCount + 1
    let tracedTail : MergeLoMachine κ ν → TraceResult (MergeLoResult κ ν) :=
      fun moved =>
        if moved.na = 1 then
          mergeLoCopyBTraced? moved
        else if mergeLoCountAtLeastWord nextACount moved.minGallop then
          mergeLoLoopTraced? fuel
            { moved with minGallop := moved.minGallop + 1 } .galloping
        else
          mergeLoLoopTraced? fuel moved (.ordinary nextACount 0)
    let referenceTail : MergeLoMachine κ ν → Option (MergeLoResult κ ν) :=
      fun moved =>
        if moved.na = 1 then
          mergeLoCopyB? moved
        else if mergeLoCountAtLeastWord nextACount moved.minGallop then
          mergeLoLoop? fuel
            { moved with minGallop := moved.minGallop + 1 } .galloping
        else
          mergeLoLoop? fuel moved (.ordinary nextACount 0)
    have hnextFuel : MergeLoFuelInvariant fuel next := by
      unfold MergeLoFuelInvariant at hfuel ⊢
      omega
    have htail : ∃ result, MergeLoCorePost origin tempTotal
      (tracedTail next) (referenceTail next) result := by
      by_cases hterminal : next.na = 1
      · have hnextNb : 0 < next.nb := by simpa [hnextNb] using hnb
        simpa [tracedTail, referenceTail, hterminal] using
          mergeLoCopyBTraced_safe origin tempTotal endIndex next hnextInv
            hterminal hnextNb
      · have hnextNaPositive : 1 < next.na := by
        have : 0 < next.na := by
          unfold MergeLoFuelInvariant at hnextFuel
          omega
        omega
        have hnextNbPositive : 0 < next.nb := by simpa [hnextNb] using hnb
        by_cases hgallop :
          mergeLoCountAtLeastWord nextACount next.minGallop
        · have hraisedInv : MergeLoMachineInvariant origin tempTotal endIndex
          { next with minGallop := next.minGallop + 1 } := by
          exact hnextInv.setMachineMinGallop _
          have hraisedFuel : MergeLoFuelInvariant fuel
            { next with minGallop := next.minGallop + 1 } := by
            exact hnextFuel
          simpa [tracedTail, referenceTail, hterminal, hgallop] using
            ih { next with minGallop := next.minGallop + 1 } .galloping
              hraisedInv hraisedFuel (by simpa using hnextNaPositive)
              (by simpa using hnextNbPositive)
        · simpa [tracedTail, referenceTail, hterminal, hgallop] using
          ih next (.ordinary nextACount 0) hnextInv hnextFuel
            hnextNaPositive hnextNbPositive
    obtain ⟨result, htail⟩ := htail
    have hcopy := MergeLoCorePost.prepend origin tempTotal
      (mergeLoCopyAIncrTraced? machine) tracedTail referenceTail next result
      hnextResult hnextSafe htail
    have hreadB := MergeLoCorePost.prepend origin tempTotal
      (TraceResult.sortSliceKeysRead? machine.state.data machine.bPos)
      (tracedAfterReads firstA) (referenceAfterReads firstA)
      firstB result hfirstBResult hfirstBSafe (by
        simpa [tracedAfterReads, referenceAfterReads, hcompare, hcompare',
          tracedTail, referenceTail, nextACount,
          erase_mergeLoCopyAIncrTraced] using hcopy)
    have hreadA := MergeLoCorePost.prepend origin tempTotal
      (TraceResult.tempPayloadRead? machine.state.a
        (Int.ofNat machine.aPos))
      (fun left =>
        (TraceResult.sortSliceKeysRead? machine.state.data machine.bPos).bind
          (tracedAfterReads left))
      (fun left => machine.state.data.read? machine.bPos |>.bind
        (referenceAfterReads left))
      firstA result hfirstAResult hfirstASafe hreadB
    refine ⟨result, ?_⟩
    simpa [mergeLoLoopTraced?, mergeLoLoop?, hguard, tracedAfterReads,
      referenceAfterReads, mergeTempRead_ofNat, mergeLoTempRead?] using hreadA
  | true =>
    have hcompare' :
      machine.state.key_compare firstB.key firstA.key = true := by
      simpa [iflt] using hcompare
    rcases mergeLoCopyBIncrTraced_safe origin tempTotal endIndex machine
      hinvariant (by omega) hnb with
      ⟨next, hnextResult, hnextSafe, hnextInv, hnextNa, hnextNb⟩
    let nextBCount := bCount + 1
    let tracedTail : MergeLoMachine κ ν → TraceResult (MergeLoResult κ ν) :=
      fun moved =>
        if moved.nb = 0 then
          mergeLoSucceedTraced? moved
        else if mergeLoCountAtLeastWord nextBCount moved.minGallop then
          mergeLoLoopTraced? fuel
            { moved with minGallop := moved.minGallop + 1 } .galloping
        else
          mergeLoLoopTraced? fuel moved (.ordinary 0 nextBCount)
    let referenceTail : MergeLoMachine κ ν → Option (MergeLoResult κ ν) :=
      fun moved =>
        if moved.nb = 0 then
          mergeLoSucceed? moved
        else if mergeLoCountAtLeastWord nextBCount moved.minGallop then
          mergeLoLoop? fuel
            { moved with minGallop := moved.minGallop + 1 } .galloping
        else
          mergeLoLoop? fuel moved (.ordinary 0 nextBCount)
    have hnextFuel : MergeLoFuelInvariant fuel next := by
      unfold MergeLoFuelInvariant at hfuel ⊢
      omega
    have htail : ∃ result, MergeLoCorePost origin tempTotal
      (tracedTail next) (referenceTail next) result := by
      by_cases hterminal : next.nb = 0
      · simpa [tracedTail, referenceTail, hterminal] using
        mergeLoSucceedTraced_safe origin tempTotal endIndex next hnextInv
      · have hnextNbPositive : 0 < next.nb := Nat.pos_of_ne_zero hterminal
        have hnextNaPositive : 1 < next.na := by simpa [hnextNa] using hna
        by_cases hgallop :
          mergeLoCountAtLeastWord nextBCount next.minGallop
        · have hraisedInv : MergeLoMachineInvariant origin tempTotal endIndex
          { next with minGallop := next.minGallop + 1 } := by
          exact hnextInv.setMachineMinGallop _
          have hraisedFuel : MergeLoFuelInvariant fuel
            { next with minGallop := next.minGallop + 1 } := by
            exact hnextFuel
          simpa [tracedTail, referenceTail, hterminal, hgallop] using
            ih { next with minGallop := next.minGallop + 1 } .galloping
              hraisedInv hraisedFuel (by simpa using hnextNaPositive)
              (by simpa using hnextNbPositive)
        · simpa [tracedTail, referenceTail, hterminal, hgallop] using
          ih next (.ordinary 0 nextBCount) hnextInv hnextFuel
            hnextNaPositive hnextNbPositive
    obtain ⟨result, htail⟩ := htail
    have hcopy := MergeLoCorePost.prepend origin tempTotal
      (mergeLoCopyBIncrTraced? machine) tracedTail referenceTail next result
      hnextResult hnextSafe htail
    have hreadB := MergeLoCorePost.prepend origin tempTotal
      (TraceResult.sortSliceKeysRead? machine.state.data machine.bPos)
      (tracedAfterReads firstA) (referenceAfterReads firstA)
      firstB result hfirstBResult hfirstBSafe (by
        simpa [tracedAfterReads, referenceAfterReads, hcompare, hcompare',
          tracedTail, referenceTail, nextBCount,
          erase_mergeLoCopyBIncrTraced] using hcopy)
    have hreadA := MergeLoCorePost.prepend origin tempTotal
      (TraceResult.tempPayloadRead? machine.state.a
        (Int.ofNat machine.aPos))
      (fun left =>
        (TraceResult.sortSliceKeysRead? machine.state.data machine.bPos).bind
          (tracedAfterReads left))
      (fun left => machine.state.data.read? machine.bPos |>.bind
        (referenceAfterReads left))
      firstA result hfirstAResult hfirstASafe hreadB
    refine ⟨result, ?_⟩
    simpa [mergeLoLoopTraced?, mergeLoLoop?, hguard, tracedAfterReads,
      referenceAfterReads, mergeTempRead_ofNat, mergeLoTempRead?] using hreadA

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoGallopSuffixTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
The weak budget is intentional: the mandatory B and A cell moves establish
the strict smaller-fuel invariant before the only recursive continuation. -/
private lemma mergeLoGallopSuffixTraced_safe
  (origin : MergeState κ ν) (tempTotal : Nat) (endIndex : Int)
  (fuel aCount : Nat) (machine : MergeLoMachine κ ν)
  (hinvariant : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hbudget : machine.na + machine.nb ≤ fuel)
  (hnb : 0 < machine.nb)
  (ih : ∀ (next : MergeLoMachine κ ν) (phase : MergeLoPhase),
    MergeLoMachineInvariant origin tempTotal endIndex next →
    MergeLoFuelInvariant fuel next → 1 < next.na → 0 < next.nb →
    ∃ result, MergeLoCorePost origin tempTotal
      (mergeLoLoopTraced? fuel next phase)
      (mergeLoLoop? fuel next phase) result) :
  let traced :=
    if machine.na = 0 then
      mergeLoSucceedTraced? machine
    else if machine.na = 1 then
      mergeLoCopyBTraced? machine
    else
      (mergeLoCopyBIncrTraced? machine).bind fun moved =>
        if moved.nb = 0 then
          mergeLoSucceedTraced? moved
        else
          (TraceResult.tempPayloadRead? moved.state.a
            (Int.ofNat moved.aPos)).bind fun firstA =>
            (gallopLeftTraced? moved.state
              (.main moved.state.data moved.bPos)
              firstA.key moved.nb 0).bind fun gallopB =>
              if gallopB.fuelExhausted then
                mergeLoFuelFailureTraced moved
              else
                let bCount := gallopB.index
                if bCount > moved.nb then
                  TraceResult.failure
                else
                  (mainDataMemmoveTraced? moved.state moved.dest moved.bPos
                    bCount).bind fun state =>
                    let moved : MergeLoMachine κ ν :=
                      { moved with
                        state := state
                        dest := moved.dest + Int.ofNat bCount
                        bPos := moved.bPos + Int.ofNat bCount
                        nb := moved.nb - bCount }
                    if moved.nb = 0 then
                      mergeLoSucceedTraced? moved
                    else
                      (mergeLoCopyAIncrTraced? moved).bind fun moved =>
                        if moved.na = 1 then
                          mergeLoCopyBTraced? moved
                        else if MIN_GALLOP.toNat ≤ aCount ∨
                          MIN_GALLOP.toNat ≤ bCount then
                          mergeLoLoopTraced? fuel moved .galloping
                        else
                          let minGallop := moved.minGallop + 1
                          let state :=
                            { moved.state with min_gallop := minGallop }
                          mergeLoLoopTraced? fuel
                            { moved with state := state, minGallop := minGallop }
                            (.ordinary 0 0)
  let reference :=
    if machine.na = 0 then
      mergeLoSucceed? machine
    else if machine.na = 1 then
      mergeLoCopyB? machine
    else do
      let moved ← mergeLoCopyBIncr? machine
      if moved.nb = 0 then
        mergeLoSucceed? moved
      else
        let firstA ← mergeLoTempRead? moved.state.a moved.aPos
        mergeLoBindOptionAcross
          (gallopLeft? moved.state moved.state.data moved.bPos
            firstA.key moved.nb 0) fun gallopB =>
          if gallopB.fuelExhausted then
            mergeLoGallopFuelFailure moved
          else
            let bCount := gallopB.index
            if bCount > moved.nb then
              none
            else do
              let data ← moved.state.data.memmove?
                moved.dest moved.bPos bCount
              let moved : MergeLoMachine κ ν :=
                { moved with
                  state := { moved.state with data := data }
                  dest := moved.dest + Int.ofNat bCount
                  bPos := moved.bPos + Int.ofNat bCount
                  nb := moved.nb - bCount }
              if moved.nb = 0 then
                mergeLoSucceed? moved
              else do
                let moved ← mergeLoCopyAIncr? moved
                if moved.na = 1 then
                  mergeLoCopyB? moved
                else if MIN_GALLOP.toNat ≤ aCount ∨
                  MIN_GALLOP.toNat ≤ bCount then
                  mergeLoLoop? fuel moved .galloping
                else
                  let minGallop := moved.minGallop + 1
                  let state := { moved.state with min_gallop := minGallop }
                  mergeLoLoop? fuel
                    { moved with state := state, minGallop := minGallop }
                    (.ordinary 0 0)
  ∃ result, MergeLoCorePost origin tempTotal traced reference result := by
  dsimp only
  by_cases hnaZero : machine.na = 0
  · simpa [hnaZero] using
    mergeLoSucceedTraced_safe origin tempTotal endIndex machine hinvariant
  · by_cases hnaOne : machine.na = 1
    · simpa [hnaZero, hnaOne] using
      mergeLoCopyBTraced_safe origin tempTotal endIndex machine hinvariant
        hnaOne hnb
    · have hna : 1 < machine.na := by omega
      rcases mergeLoCopyBIncrTraced_safe origin tempTotal endIndex machine
        hinvariant (by omega) hnb with
        ⟨afterB, hafterBResult, hafterBSafe, hafterBInv, hafterBNa,
          hafterBNb⟩
      let tracedAfterB := fun (moved : MergeLoMachine κ ν) =>
        if moved.nb = 0 then
          mergeLoSucceedTraced? moved
        else
          (TraceResult.tempPayloadRead? moved.state.a
            (Int.ofNat moved.aPos)).bind fun firstA =>
            (gallopLeftTraced? moved.state
              (.main moved.state.data moved.bPos)
              firstA.key moved.nb 0).bind fun gallopB =>
              if gallopB.fuelExhausted then
                mergeLoFuelFailureTraced moved
              else
                let bCount := gallopB.index
                if bCount > moved.nb then
                  TraceResult.failure
                else
                  (mainDataMemmoveTraced? moved.state moved.dest moved.bPos
                    bCount).bind fun state =>
                    let moved : MergeLoMachine κ ν :=
                      { moved with
                        state := state
                        dest := moved.dest + Int.ofNat bCount
                        bPos := moved.bPos + Int.ofNat bCount
                        nb := moved.nb - bCount }
                    if moved.nb = 0 then
                      mergeLoSucceedTraced? moved
                    else
                      (mergeLoCopyAIncrTraced? moved).bind fun moved =>
                        if moved.na = 1 then
                          mergeLoCopyBTraced? moved
                        else if MIN_GALLOP.toNat ≤ aCount ∨
                          MIN_GALLOP.toNat ≤ bCount then
                          mergeLoLoopTraced? fuel moved .galloping
                        else
                          let minGallop := moved.minGallop + 1
                          let state :=
                            { moved.state with min_gallop := minGallop }
                          mergeLoLoopTraced? fuel
                            { moved with state := state, minGallop := minGallop }
                            (.ordinary 0 0)
      let referenceAfterB := fun (moved : MergeLoMachine κ ν) =>
        if moved.nb = 0 then
          mergeLoSucceed? moved
        else do
          let firstA ← mergeLoTempRead? moved.state.a moved.aPos
          mergeLoBindOptionAcross
            (gallopLeft? moved.state moved.state.data moved.bPos
              firstA.key moved.nb 0) fun gallopB =>
            if gallopB.fuelExhausted then
              mergeLoGallopFuelFailure moved
            else
              let bCount := gallopB.index
              if bCount > moved.nb then
                none
              else do
                let data ← moved.state.data.memmove?
                  moved.dest moved.bPos bCount
                let moved : MergeLoMachine κ ν :=
                  { moved with
                    state := { moved.state with data := data }
                    dest := moved.dest + Int.ofNat bCount
                    bPos := moved.bPos + Int.ofNat bCount
                    nb := moved.nb - bCount }
                if moved.nb = 0 then
                  mergeLoSucceed? moved
                else do
                  let moved ← mergeLoCopyAIncr? moved
                  if moved.na = 1 then
                    mergeLoCopyB? moved
                  else if MIN_GALLOP.toNat ≤ aCount ∨
                    MIN_GALLOP.toNat ≤ bCount then
                    mergeLoLoop? fuel moved .galloping
                  else
                    let minGallop := moved.minGallop + 1
                    let state := { moved.state with min_gallop := minGallop }
                    mergeLoLoop? fuel
                      { moved with state := state, minGallop := minGallop }
                      (.ordinary 0 0)
      have hafterBBudget : afterB.na + afterB.nb < fuel := by
        omega
      have htail : ∃ result, MergeLoCorePost origin tempTotal
        (tracedAfterB afterB) (referenceAfterB afterB) result := by
        by_cases hterminalB : afterB.nb = 0
        · simpa [tracedAfterB, referenceAfterB, hterminalB] using
          mergeLoSucceedTraced_safe origin tempTotal endIndex afterB
            hafterBInv
        · have hafterBNbPositive : 0 < afterB.nb :=
          Nat.pos_of_ne_zero hterminalB
          rcases hafterBInv.tempReadable (by omega) with
            ⟨firstA, hfirstA⟩
          have hfirstAResult :
            (TraceResult.tempPayloadRead? afterB.state.a
              (Int.ofNat afterB.aPos)).result = some firstA := by
            change (TraceResult.tempPayloadRead? afterB.state.a
              (Int.ofNat afterB.aPos)).erase = some firstA
            rwa [TraceResult.erase_tempPayloadRead]
          have hfirstASafe := mergeLoTempReadTraced_safe afterB.state.a
            (Int.ofNat afterB.aPos)
            (hafterBInv.aPosInBounds (by omega)) hafterBInv.tempLive
          rcases mergeLoTempRun_exists_of_initialized afterB.state.a
            afterB.aPos afterB.na (by
              intro offset hoffset
              rcases hafterBInv.tempActiveValuesMode offset hoffset with
                ⟨entry, hentry, _⟩
              refine ⟨entry, ?_⟩
              rw [erase_mergeTempRead] at hentry
              have hsum : Int.ofNat afterB.aPos + Int.ofNat offset =
                Int.ofNat (afterB.aPos + offset) := by
                simp only [Int.ofNat_eq_natCast, Nat.cast_add]
              rw [hsum, mergeTempRead_ofNat] at hentry
              exact hentry) with ⟨_activeA, _hactiveA⟩
          rcases gallopLeft_main_safe afterB.state afterB.state.data
            afterB.bPos firstA.key afterB.nb 0
            hafterBInv.rightValidRange hafterBNbPositive (by omega)
            hafterBInv.rightWordBound with
            ⟨gallopB, hgallopBResult, hgallopBFuel, hbCount,
              hgallopBTraceFuel, hgallopBNoPush, hgallopBBounds,
              hgallopBLive, hgallopBErase⟩
          have hgallopBSafe : MovementTraceSafe
            (gallopLeftTraced? afterB.state
              (.main afterB.state.data afterB.bPos)
              firstA.key afterB.nb 0) :=
            ⟨hgallopBTraceFuel, hgallopBNoPush, hgallopBBounds,
              hgallopBLive⟩
          let bCount := gallopB.index
          have hbNotGreater : ¬ afterB.nb < bCount := by
            dsimp [bCount]
            omega
          rcases mainDataMemmoveTraced_safe afterB.state afterB.dest
            afterB.bPos bCount hafterBInv.tempInvariant
            hafterBInv.tempLive hafterBInv.valuesMode
            (hafterBInv.destTotalRange bCount (by omega))
            (hafterBInv.rightRange bCount hbCount) with ⟨movedState, hmove⟩
          let moved : MergeLoMachine κ ν :=
            { afterB with
              state := movedState
              dest := afterB.dest + Int.ofNat bCount
              bPos := afterB.bPos + Int.ofNat bCount
              nb := afterB.nb - bCount }
          have hmovedTemp := mainDataMemmoveTraced_temp_eq_of_result
            afterB.state movedState afterB.dest afterB.bPos bCount hmove.success
          have hmovedInv : MergeLoMachineInvariant origin tempTotal endIndex moved :=
            hafterBInv.copyBBlock bCount hbCount movedState hmove.frame
              hmovedTemp hmove.valuesMode
          have hmovedNa : moved.na = afterB.na := rfl
          have hmovedNbEq : moved.nb = afterB.nb - bCount := rfl
          let tracedAfterMove := fun (count : Nat)
            (current : MergeLoMachine κ ν) =>
            if current.nb = 0 then
              mergeLoSucceedTraced? current
            else
              (mergeLoCopyAIncrTraced? current).bind fun next =>
                if next.na = 1 then
                  mergeLoCopyBTraced? next
                else if MIN_GALLOP.toNat ≤ aCount ∨
                  MIN_GALLOP.toNat ≤ count then
                  mergeLoLoopTraced? fuel next .galloping
                else
                  let minGallop := next.minGallop + 1
                  let state := { next.state with min_gallop := minGallop }
                  mergeLoLoopTraced? fuel
                    { next with state := state, minGallop := minGallop }
                    (.ordinary 0 0)
          let referenceAfterMove := fun (count : Nat)
            (current : MergeLoMachine κ ν) =>
            if current.nb = 0 then
              mergeLoSucceed? current
            else do
              let next ← mergeLoCopyAIncr? current
              if next.na = 1 then
                mergeLoCopyB? next
              else if MIN_GALLOP.toNat ≤ aCount ∨
                MIN_GALLOP.toNat ≤ count then
                mergeLoLoop? fuel next .galloping
              else
                let minGallop := next.minGallop + 1
                let state := { next.state with min_gallop := minGallop }
                mergeLoLoop? fuel
                  { next with state := state, minGallop := minGallop }
                  (.ordinary 0 0)
          have hafterMove : ∃ result, MergeLoCorePost origin tempTotal
            (tracedAfterMove bCount moved)
            (referenceAfterMove bCount moved) result := by
            by_cases hterminal : moved.nb = 0
            · simpa [tracedAfterMove, referenceAfterMove, hterminal] using
              mergeLoSucceedTraced_safe origin tempTotal endIndex moved
                hmovedInv
            · have hmovedNbPositive : 0 < moved.nb :=
              Nat.pos_of_ne_zero hterminal
              rcases mergeLoCopyAIncrTraced_safe origin tempTotal endIndex
                moved hmovedInv (by
                  rw [hmovedNa, hafterBNa]
                  exact Nat.zero_lt_of_lt hna) with
                ⟨afterA, hafterAResult, hafterASafe, hafterAInv,
                  hafterANa, hafterANb⟩
              let tracedFinal := fun (next : MergeLoMachine κ ν) =>
                if next.na = 1 then
                  mergeLoCopyBTraced? next
                else if MIN_GALLOP.toNat ≤ aCount ∨
                  MIN_GALLOP.toNat ≤ bCount then
                  mergeLoLoopTraced? fuel next .galloping
                else
                  let minGallop := next.minGallop + 1
                  let state := { next.state with min_gallop := minGallop }
                  mergeLoLoopTraced? fuel
                    { next with state := state, minGallop := minGallop }
                    (.ordinary 0 0)
              let referenceFinal := fun (next : MergeLoMachine κ ν) =>
                if next.na = 1 then
                  mergeLoCopyB? next
                else if MIN_GALLOP.toNat ≤ aCount ∨
                  MIN_GALLOP.toNat ≤ bCount then
                  mergeLoLoop? fuel next .galloping
                else
                  let minGallop := next.minGallop + 1
                  let state := { next.state with min_gallop := minGallop }
                  mergeLoLoop? fuel
                    { next with state := state, minGallop := minGallop }
                    (.ordinary 0 0)
              have hfinal : ∃ result, MergeLoCorePost origin tempTotal
                (tracedFinal afterA) (referenceFinal afterA) result := by
                by_cases hterminalA : afterA.na = 1
                · have hafterANbPositive : 0 < afterA.nb := by
                  simpa [hafterANb] using hmovedNbPositive
                  simpa [tracedFinal, referenceFinal, hterminalA] using
                    mergeLoCopyBTraced_safe origin tempTotal endIndex afterA
                      hafterAInv hterminalA hafterANbPositive
                · have hafterANaPositive : 1 < afterA.na := by
                  have : 0 < afterA.na := by
                    rw [hafterANa, hmovedNa]
                    omega
                  omega
                  have hafterANbPositive : 0 < afterA.nb := by
                    simpa [hafterANb] using hmovedNbPositive
                  have hafterAFuel : MergeLoFuelInvariant fuel afterA := by
                    unfold MergeLoFuelInvariant
                    rw [hafterANa, hafterANb, hmovedNa, hmovedNbEq]
                    omega
                  by_cases hstay : MIN_GALLOP.toNat ≤ aCount ∨
                    MIN_GALLOP.toNat ≤ bCount
                  · simpa [tracedFinal, referenceFinal, hterminalA, hstay]
                    using ih afterA .galloping hafterAInv hafterAFuel
                      hafterANaPositive hafterANbPositive
                  · let minGallop := afterA.minGallop + 1
                    let adjusted : MergeLoMachine κ ν :=
                      { afterA with
                        state := { afterA.state with min_gallop := minGallop }
                        minGallop := minGallop }
                    have hadjustedInv : MergeLoMachineInvariant origin tempTotal
                      endIndex adjusted := by
                      exact hafterAInv.setMinGallop minGallop
                    have hadjustedFuel : MergeLoFuelInvariant fuel adjusted := by
                      exact hafterAFuel
                    simpa [tracedFinal, referenceFinal, hterminalA, hstay,
                      adjusted, minGallop] using
                      ih adjusted (.ordinary 0 0) hadjustedInv hadjustedFuel
                        (by simpa [adjusted] using hafterANaPositive)
                        (by simpa [adjusted] using hafterANbPositive)
              obtain ⟨result, hfinal⟩ := hfinal
              exact ⟨result, by
                simpa [tracedAfterMove, referenceAfterMove, hterminal,
                  tracedFinal, referenceFinal] using
                  MergeLoCorePost.prepend origin tempTotal
                    (mergeLoCopyAIncrTraced? moved) tracedFinal referenceFinal
                    afterA result hafterAResult hafterASafe hfinal⟩
          obtain ⟨result, hafterMove⟩ := hafterMove
          have hmovePost := MergeLoCorePost.prepend origin tempTotal
            (mainDataMemmoveTraced? afterB.state afterB.dest afterB.bPos bCount)
            (fun state => tracedAfterMove bCount
              { afterB with
                state := state
                dest := afterB.dest + Int.ofNat bCount
                bPos := afterB.bPos + Int.ofNat bCount
                nb := afterB.nb - bCount })
            (fun state => referenceAfterMove bCount
              { afterB with
                state := state
                dest := afterB.dest + Int.ofNat bCount
                bPos := afterB.bPos + Int.ofNat bCount
                nb := afterB.nb - bCount })
            movedState result hmove.success hmove.traceSafe hafterMove
          let tracedAfterGallop := fun (g : GallopResult) =>
            if g.fuelExhausted then
              mergeLoFuelFailureTraced afterB
            else
              let count := g.index
              if count > afterB.nb then
                TraceResult.failure
              else
                (mainDataMemmoveTraced? afterB.state afterB.dest afterB.bPos
                  count).bind fun state =>
                    tracedAfterMove count
                      { afterB with
                        state := state
                        dest := afterB.dest + Int.ofNat count
                        bPos := afterB.bPos + Int.ofNat count
                        nb := afterB.nb - count }
          let referenceAfterGallop := fun (g : GallopResult) =>
            if g.fuelExhausted then
              mergeLoGallopFuelFailure afterB
            else
              let count := g.index
              if count > afterB.nb then
                none
              else do
                let data ← afterB.state.data.memmove?
                  afterB.dest afterB.bPos count
                referenceAfterMove count
                  { afterB with
                    state := { afterB.state with data := data }
                    dest := afterB.dest + Int.ofNat count
                    bPos := afterB.bPos + Int.ofNat count
                    nb := afterB.nb - count }
          have hgallopPost := MergeLoCorePost.prepend origin tempTotal
            (gallopLeftTraced? afterB.state
              (.main afterB.state.data afterB.bPos)
              firstA.key afterB.nb 0)
            tracedAfterGallop referenceAfterGallop gallopB result
            hgallopBResult hgallopBSafe (by
              simpa [tracedAfterGallop, referenceAfterGallop, hgallopBFuel,
                bCount, hbCount, hbNotGreater, mainDataMemmove?,
                erase_mainDataMemmoveTraced, Option.bind_assoc] using hmovePost)
          have hreadPost := MergeLoCorePost.prepend origin tempTotal
            (TraceResult.tempPayloadRead? afterB.state.a
              (Int.ofNat afterB.aPos))
            (fun entry =>
              (gallopLeftTraced? afterB.state
                (.main afterB.state.data afterB.bPos)
                entry.key afterB.nb 0).bind tracedAfterGallop)
            (fun entry =>
              mergeLoBindOptionAcross
                (gallopLeft? afterB.state afterB.state.data afterB.bPos
                  entry.key afterB.nb 0) referenceAfterGallop)
            firstA result hfirstAResult hfirstASafe (by
              have hbind :
                (gallopLeft? afterB.state afterB.state.data afterB.bPos
                  firstA.key afterB.nb 0).bind referenceAfterGallop =
                  mergeLoBindOptionAcross
                    (gallopLeft? afterB.state afterB.state.data afterB.bPos
                      firstA.key afterB.nb 0) referenceAfterGallop := by
                cases gallopLeft? afterB.state afterB.state.data afterB.bPos
                  firstA.key afterB.nb 0 <;> rfl
              simpa [hgallopBErase, hbind] using hgallopPost)
          exact ⟨result, by
            simpa [tracedAfterB, referenceAfterB, hterminalB,
              tracedAfterGallop, referenceAfterGallop, tracedAfterMove,
              referenceAfterMove, mergeLoTempRead?, mergeTempRead_ofNat]
              using hreadPost⟩
      obtain ⟨result, htail⟩ := htail
      exact ⟨result, by
        simpa [hnaZero, hnaOne, tracedAfterB, referenceAfterB,
          erase_mergeLoCopyBIncrTraced] using
          MergeLoCorePost.prepend origin tempTotal
            (mergeLoCopyBIncrTraced? machine) tracedAfterB referenceAfterB
            afterB result hafterBResult hafterBSafe htail⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoGallopingTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
allowed to differ briefly from `state.min_gallop`: the straight-to-gallop
transition increments only the local field, exactly as in the reviewed
transcription, and this step immediately writes the decreased threshold back
to the state. -/
private lemma mergeLoGallopingTraced_safe
  (origin : MergeState κ ν) (tempTotal : Nat) (endIndex : Int)
  (fuel : Nat) (machine : MergeLoMachine κ ν)
  (hinvariant : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hfuel : MergeLoFuelInvariant (fuel + 1) machine)
  (hna : 1 < machine.na) (hnb : 0 < machine.nb)
  (ih : ∀ (next : MergeLoMachine κ ν) (phase : MergeLoPhase),
    MergeLoMachineInvariant origin tempTotal endIndex next →
    MergeLoFuelInvariant fuel next → 1 < next.na → 0 < next.nb →
    ∃ result, MergeLoCorePost origin tempTotal
      (mergeLoLoopTraced? fuel next phase)
      (mergeLoLoop? fuel next phase) result) :
  ∃ result, MergeLoCorePost origin tempTotal
    (mergeLoLoopTraced? (fuel + 1) machine .galloping)
    (mergeLoLoop? (fuel + 1) machine .galloping) result := by
  have hguard : ¬ (machine.na ≤ 1 ∨ machine.nb = 0) := by omega
  let minGallop :=
    if (1 : PySSize).slt machine.minGallop then
      machine.minGallop - 1
    else machine.minGallop
  let adjusted : MergeLoMachine κ ν :=
    { machine with
      state := { machine.state with min_gallop := minGallop }
      minGallop := minGallop }
  have hadjustedInv : MergeLoMachineInvariant origin tempTotal endIndex adjusted :=
    hinvariant.setMinGallop minGallop
  have hadjustedNa : adjusted.na = machine.na := rfl
  have hadjustedNb : adjusted.nb = machine.nb := rfl
  rcases SortSlice.read_eq_some_of_indexInBounds adjusted.state.data adjusted.bPos
    (hadjustedInv.bPosInBounds (by simpa [hadjustedNb] using hnb)) with
    ⟨firstB, hfirstB⟩
  have hfirstBResult :
    (TraceResult.sortSliceKeysRead? adjusted.state.data adjusted.bPos).result =
      some firstB := by
    change adjusted.state.data.read? adjusted.bPos = some firstB
    exact hfirstB
  have hfirstBSafe := mergeLoMainKeyReadTraced_safe adjusted.state.data
    adjusted.bPos (hadjustedInv.bPosInBounds (by simpa [hadjustedNb] using hnb))
  have hinitialized : MergeLoTempRangeInitialized adjusted.state.a
    adjusted.aPos adjusted.na := by
    intro offset hoffset
    rcases hadjustedInv.tempActiveValuesMode offset hoffset with
      ⟨entry, hentry, _⟩
    refine ⟨entry, ?_⟩
    rw [erase_mergeTempRead] at hentry
    have hsum : Int.ofNat adjusted.aPos + Int.ofNat offset =
      Int.ofNat (adjusted.aPos + offset) := by
      simp only [Int.ofNat_eq_natCast, Nat.cast_add]
    rwa [hsum, mergeTempRead_ofNat] at hentry
  rcases mergeLoTempRun_exists_of_initialized adjusted.state.a adjusted.aPos
    adjusted.na hinitialized with ⟨activeA, hactiveA⟩
  have hactiveResult :
    (mergeLoTraceOption
      (mergeLoTempRun? adjusted.state.a adjusted.aPos adjusted.na)).result =
      some activeA := by
    simp [mergeLoTraceOption, hactiveA, TraceResult.pure]
  have hactiveSafe : MovementTraceSafe
    (mergeLoTraceOption
      (mergeLoTempRun? adjusted.state.a adjusted.aPos adjusted.na)) := by
    simpa [mergeLoTraceOption, hactiveA] using
      (MovementTraceSafe.pure activeA)
  rcases gallopRight_safe adjusted.state
    (.temporary adjusted.state.a (Int.ofNat adjusted.aPos)) activeA 0
    firstB.key adjusted.na 0 hadjustedInv.temporaryValidRange
    hadjustedInv.tempLive
    (tempRun_agreesWithSlice_of_eq_some adjusted.state.a adjusted.aPos
      adjusted.na activeA hactiveA)
    (by rw [hadjustedNa]; omega) (by omega)
    hadjustedInv.leftWordBound with
    ⟨gallopA, hgallopAResult, hgallopAFuel, haCount,
      hgallopATraceFuel, hgallopANoPush, hgallopABounds,
      hgallopALive, hgallopAErase⟩
  have hgallopASafe : MovementTraceSafe
    (gallopRightTraced? adjusted.state
      (.temporary adjusted.state.a (Int.ofNat adjusted.aPos))
      firstB.key adjusted.na 0) :=
    ⟨hgallopATraceFuel, hgallopANoPush, hgallopABounds, hgallopALive⟩
  let aCount := gallopA.index
  have haNotGreater : ¬ adjusted.na < aCount := by
    dsimp [aCount]
    omega
  rcases tempToMainMemcpyTraced_post (.lo .gallopTempToData)
    mergeLoGallopTempToDataPermit aCount adjusted.state adjusted.dest
    (Int.ofNat adjusted.aPos) (hadjustedInv.destRange aCount haCount)
    (hadjustedInv.tempPrefixInBounds aCount haCount)
    (hadjustedInv.tempPrefixValuesMode aCount haCount)
    hadjustedInv.tempInvariant hadjustedInv.tempLive
    hadjustedInv.valuesMode with ⟨copiedState, hcopy⟩
  let afterA : MergeLoMachine κ ν :=
    { adjusted with
      state := copiedState
      dest := adjusted.dest + Int.ofNat aCount
      aPos := adjusted.aPos + aCount
      na := adjusted.na - aCount }
  have hcopyCore : tempToMainMemcpy? aCount adjusted.state adjusted.dest
    (Int.ofNat adjusted.aPos) = some copiedState := by
    rwa [← hcopy.exactErasure]
  have hcopyTemp := tempToMainMemcpy_temp_eq_of_eq_some aCount adjusted.state
    copiedState adjusted.dest (Int.ofNat adjusted.aPos) hcopyCore
  have hafterAInv : MergeLoMachineInvariant origin tempTotal endIndex afterA :=
    hadjustedInv.copyABlock aCount haCount copiedState hcopy.frame hcopyTemp
      hcopy.valuesMode
  have hafterABudget : afterA.na + afterA.nb ≤ fuel := by
    unfold MergeLoFuelInvariant at hfuel
    dsimp [afterA, adjusted]
    omega
  have hafterANb : 0 < afterA.nb := by
    dsimp [afterA, adjusted]
    exact hnb
  let tracedAfterCopy := fun (count : Nat) (current : MergeLoMachine κ ν) =>
    if current.na = 0 then
      mergeLoSucceedTraced? current
    else if current.na = 1 then
      mergeLoCopyBTraced? current
    else
      (mergeLoCopyBIncrTraced? current).bind fun moved =>
        if moved.nb = 0 then
          mergeLoSucceedTraced? moved
        else
          (TraceResult.tempPayloadRead? moved.state.a
            (Int.ofNat moved.aPos)).bind fun firstA =>
            (gallopLeftTraced? moved.state
              (.main moved.state.data moved.bPos)
              firstA.key moved.nb 0).bind fun gallopB =>
              if gallopB.fuelExhausted then
                mergeLoFuelFailureTraced moved
              else
                let bCount := gallopB.index
                if bCount > moved.nb then
                  TraceResult.failure
                else
                  (mainDataMemmoveTraced? moved.state moved.dest moved.bPos
                    bCount).bind fun state =>
                    let moved : MergeLoMachine κ ν :=
                      { moved with
                        state := state
                        dest := moved.dest + Int.ofNat bCount
                        bPos := moved.bPos + Int.ofNat bCount
                        nb := moved.nb - bCount }
                    if moved.nb = 0 then
                      mergeLoSucceedTraced? moved
                    else
                      (mergeLoCopyAIncrTraced? moved).bind fun moved =>
                        if moved.na = 1 then
                          mergeLoCopyBTraced? moved
                        else if MIN_GALLOP.toNat ≤ count ∨
                          MIN_GALLOP.toNat ≤ bCount then
                          mergeLoLoopTraced? fuel moved .galloping
                        else
                          let threshold := moved.minGallop + 1
                          let state :=
                            { moved.state with min_gallop := threshold }
                          mergeLoLoopTraced? fuel
                            { moved with state := state, minGallop := threshold }
                            (.ordinary 0 0)
  let referenceAfterCopy := fun (count : Nat)
    (current : MergeLoMachine κ ν) =>
    if current.na = 0 then
      mergeLoSucceed? current
    else if current.na = 1 then
      mergeLoCopyB? current
    else do
      let moved ← mergeLoCopyBIncr? current
      if moved.nb = 0 then
        mergeLoSucceed? moved
      else
        let firstA ← mergeLoTempRead? moved.state.a moved.aPos
        mergeLoBindOptionAcross
          (gallopLeft? moved.state moved.state.data moved.bPos
            firstA.key moved.nb 0) fun gallopB =>
          if gallopB.fuelExhausted then
            mergeLoGallopFuelFailure moved
          else
            let bCount := gallopB.index
            if bCount > moved.nb then
              none
            else do
              let data ← moved.state.data.memmove?
                moved.dest moved.bPos bCount
              let moved : MergeLoMachine κ ν :=
                { moved with
                  state := { moved.state with data := data }
                  dest := moved.dest + Int.ofNat bCount
                  bPos := moved.bPos + Int.ofNat bCount
                  nb := moved.nb - bCount }
              if moved.nb = 0 then
                mergeLoSucceed? moved
              else do
                let moved ← mergeLoCopyAIncr? moved
                if moved.na = 1 then
                  mergeLoCopyB? moved
                else if MIN_GALLOP.toNat ≤ count ∨
                  MIN_GALLOP.toNat ≤ bCount then
                  mergeLoLoop? fuel moved .galloping
                else
                  let threshold := moved.minGallop + 1
                  let state := { moved.state with min_gallop := threshold }
                  mergeLoLoop? fuel
                    { moved with state := state, minGallop := threshold }
                    (.ordinary 0 0)
  rcases mergeLoGallopSuffixTraced_safe origin tempTotal endIndex fuel aCount
    afterA hafterAInv hafterABudget hafterANb ih with ⟨result, hsuffix⟩
  have hcopyPost := MergeLoCorePost.prepend origin tempTotal
    (tempToMainMemcpyTraced? (.lo .gallopTempToData)
      mergeLoGallopTempToDataPermit aCount adjusted.state adjusted.dest
      (Int.ofNat adjusted.aPos))
    (fun state => tracedAfterCopy aCount
      { adjusted with
        state := state
        dest := adjusted.dest + Int.ofNat aCount
        aPos := adjusted.aPos + aCount
        na := adjusted.na - aCount })
    (fun state => referenceAfterCopy aCount
      { adjusted with
        state := state
        dest := adjusted.dest + Int.ofNat aCount
        aPos := adjusted.aPos + aCount
        na := adjusted.na - aCount })
    copiedState result hcopy.success hcopy.traceSafe (by
      simpa [tracedAfterCopy, referenceAfterCopy, afterA] using hsuffix)
  let tracedAfterGallop := fun (g : GallopResult) =>
    if g.fuelExhausted then
      mergeLoFuelFailureTraced adjusted
    else
      let count := g.index
      if count > adjusted.na then
        TraceResult.failure
      else
        (tempToMainMemcpyTraced? (.lo .gallopTempToData)
          mergeLoGallopTempToDataPermit count adjusted.state adjusted.dest
          (Int.ofNat adjusted.aPos)).bind fun state =>
            tracedAfterCopy count
              { adjusted with
                state := state
                dest := adjusted.dest + Int.ofNat count
                aPos := adjusted.aPos + count
                na := adjusted.na - count }
  let referenceAfterGallop := fun (g : GallopResult) =>
    if g.fuelExhausted then
      mergeLoGallopFuelFailure adjusted
    else
      let count := g.index
      if count > adjusted.na then
        none
      else do
        let state ← mergeLoMemcpyTempToData? .gallopTempToData rfl count
          adjusted.state adjusted.dest adjusted.aPos
        referenceAfterCopy count
          { adjusted with
            state := state
            dest := adjusted.dest + Int.ofNat count
            aPos := adjusted.aPos + count
            na := adjusted.na - count }
  have hgallopPost := MergeLoCorePost.prepend origin tempTotal
    (gallopRightTraced? adjusted.state
      (.temporary adjusted.state.a (Int.ofNat adjusted.aPos))
      firstB.key adjusted.na 0)
    tracedAfterGallop referenceAfterGallop gallopA result
    hgallopAResult hgallopASafe (by
      let continuation := fun state => referenceAfterCopy aCount
        { adjusted with
          state := state
          dest := adjusted.dest + Int.ofNat aCount
          aPos := adjusted.aPos + aCount
          na := adjusted.na - aCount }
      have href :
        (tempToMainMemcpyTraced? (.lo .gallopTempToData)
          mergeLoGallopTempToDataPermit aCount adjusted.state
          adjusted.dest (Int.ofNat adjusted.aPos)).erase.bind continuation =
          (mergeLoMemcpyTempToData? .gallopTempToData rfl aCount
            adjusted.state adjusted.dest adjusted.aPos).bind continuation :=
        calc
          _ = (tempToMainMemcpy? aCount adjusted.state adjusted.dest
            (Int.ofNat adjusted.aPos)).bind continuation :=
            congrArg (fun option => option.bind continuation)
              (erase_tempToMainMemcpyTraced (.lo .gallopTempToData)
                mergeLoGallopTempToDataPermit aCount adjusted.state
                adjusted.dest (Int.ofNat adjusted.aPos))
          _ = _ := congrArg (fun option => option.bind continuation)
            (tempToMainMemcpy_eq_mergeLo .gallopTempToData rfl aCount
              adjusted.state adjusted.dest adjusted.aPos)
      have htagged := MergeLoCorePost.reference_eq origin tempTotal _ _ _
        result href hcopyPost
      simpa [tracedAfterGallop, referenceAfterGallop, hgallopAFuel,
        haNotGreater, aCount, continuation] using htagged)
  let tracedAfterSlice := fun (_ : SortSlice κ ν) =>
    (gallopRightTraced? adjusted.state
      (.temporary adjusted.state.a (Int.ofNat adjusted.aPos))
      firstB.key adjusted.na 0).bind tracedAfterGallop
  let referenceAfterSlice := fun (slice : SortSlice κ ν) =>
    mergeLoBindOptionAcross
      (gallopRight? adjusted.state slice 0 firstB.key adjusted.na 0)
      referenceAfterGallop
  have hslicePost := MergeLoCorePost.prepend origin tempTotal
    (mergeLoTraceOption
      (mergeLoTempRun? adjusted.state.a adjusted.aPos adjusted.na))
    tracedAfterSlice referenceAfterSlice activeA result hactiveResult hactiveSafe
    (by
      have hbind :
        (gallopRight? adjusted.state activeA 0 firstB.key adjusted.na 0).bind
          referenceAfterGallop =
          mergeLoBindOptionAcross
            (gallopRight? adjusted.state activeA 0 firstB.key adjusted.na 0)
            referenceAfterGallop := by
        cases gallopRight? adjusted.state activeA 0 firstB.key adjusted.na 0 <;>
          rfl
      have href :
        (gallopRightTraced? adjusted.state
          (.temporary adjusted.state.a (Int.ofNat adjusted.aPos))
          firstB.key adjusted.na 0).erase.bind referenceAfterGallop =
          mergeLoBindOptionAcross
            (gallopRight? adjusted.state activeA 0 firstB.key adjusted.na 0)
            referenceAfterGallop := by
        calc
          _ = (gallopRight? adjusted.state activeA 0 firstB.key adjusted.na 0).bind
            referenceAfterGallop :=
            congrArg (fun option => option.bind referenceAfterGallop)
              hgallopAErase
          _ = _ := hbind
      exact MergeLoCorePost.reference_eq origin tempTotal _ _ _ result href
        hgallopPost)
  let tracedAfterFirstB := fun (entry : SortSliceEntry κ ν) =>
    (mergeLoTraceOption
      (mergeLoTempRun? adjusted.state.a adjusted.aPos adjusted.na)).bind
        fun _ =>
          (gallopRightTraced? adjusted.state
            (.temporary adjusted.state.a (Int.ofNat adjusted.aPos))
            entry.key adjusted.na 0).bind tracedAfterGallop
  let referenceAfterFirstB := fun (entry : SortSliceEntry κ ν) =>
    (mergeLoTempRun? adjusted.state.a adjusted.aPos adjusted.na).bind fun slice =>
      mergeLoBindOptionAcross
        (gallopRight? adjusted.state slice 0 entry.key adjusted.na 0)
        referenceAfterGallop
  have hfirstBPost := MergeLoCorePost.prepend origin tempTotal
    (TraceResult.sortSliceKeysRead? adjusted.state.data adjusted.bPos)
    tracedAfterFirstB referenceAfterFirstB firstB result hfirstBResult hfirstBSafe
    (by simpa [tracedAfterFirstB, referenceAfterFirstB, tracedAfterSlice,
      referenceAfterSlice, mergeLoTraceOption_erase] using hslicePost)
  refine ⟨result, ?_⟩
  simpa [mergeLoLoopTraced?, mergeLoLoop?, mergeLoGallopRoundTraced?,
    mergeLoGallopRound?, hguard, minGallop, adjusted, tracedAfterFirstB,
    referenceAfterFirstB, tracedAfterSlice, referenceAfterSlice,
    tracedAfterGallop, referenceAfterGallop, tracedAfterCopy,
    referenceAfterCopy, mergeLoBindOptionAcross] using hfirstBPost

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoLoopTraced_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
zero-fuel marker and is decreased only after at least one real merge move. -/
private lemma mergeLoLoopTraced_safe
  (origin : MergeState κ ν) (tempTotal : Nat) (endIndex : Int)
  (fuel : Nat) (machine : MergeLoMachine κ ν) (phase : MergeLoPhase)
  (hinvariant : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hfuel : MergeLoFuelInvariant fuel machine)
  (hna : 1 < machine.na) (hnb : 0 < machine.nb) :
  ∃ result, MergeLoCorePost origin tempTotal
    (mergeLoLoopTraced? fuel machine phase)
    (mergeLoLoop? fuel machine phase) result := by
  induction fuel generalizing machine phase with
  | zero =>
    unfold MergeLoFuelInvariant at hfuel
    omega
  | succ fuel ih =>
    cases phase with
    | ordinary aCount bCount =>
      exact mergeLoOrdinaryTraced_safe origin tempTotal endIndex fuel machine
        aCount bCount hinvariant hfuel hna hnb ih
    | galloping =>
      exact mergeLoGallopingTraced_safe origin tempTotal endIndex fuel machine
        hinvariant hfuel hna hnb ih

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[hasAccess_bind_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma hasAccess_bind_left
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
[hasAccess_bind_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma hasAccess_bind_right
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
[hasTempAccess_bind_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma hasTempAccess_bind_left
  (current : TraceResult α) (next : α → TraceResult β)
  (kind : AccessKind) (hcurrent : current.trace.HasTempAccess kind) :
  (current.bind next).trace.HasTempAccess kind := by
  obtain ⟨backing, hcurrent⟩ := hcurrent
  exact ⟨backing, hasAccess_bind_left current next kind
    (.tempPayload backing) hcurrent⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[hasTempAccess_bind_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma hasTempAccess_bind_right
  (current : TraceResult α) (next : α → TraceResult β)
  (value : α) (kind : AccessKind)
  (hresult : current.result = some value)
  (hnext : (next value).trace.HasTempAccess kind) :
  (current.bind next).trace.HasTempAccess kind := by
  obtain ⟨backing, hnext⟩ := hnext
  exact ⟨backing, hasAccess_bind_right current next value kind
    (.tempPayload backing) hresult hnext⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[tempPayloadRead_hasTempAccess](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma tempPayloadRead_hasTempAccess
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
[tempToMainCellTraced_hasTempRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma tempToMainCellTraced_hasTempRead
  (state : MergeState κ ν) (mainDst tempSrc : Int) :
  (tempToMainCellTraced? state mainDst tempSrc).trace.HasTempAccess .read := by
  have hkey : (tempToMainKeyTraced? state mainDst tempSrc).trace.HasTempAccess
    .read := by
    unfold tempToMainKeyTraced?
    exact hasTempAccess_bind_left _ _ .read
      (tempPayloadRead_hasTempAccess state.a tempSrc)
  unfold tempToMainCellTraced?
  exact hasTempAccess_bind_left _ _ .read hkey

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoSucceedTraced_hasTempRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoSucceedTraced_hasTempRead
  (origin : MergeState κ ν) (tempTotal : Nat) (endIndex : Int)
  (machine : MergeLoMachine κ ν)
  (hinvariant : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hna : 0 < machine.na) :
  (mergeLoSucceedTraced? machine).trace.HasTempAccess .read := by
  have hmain := hinvariant.destRange machine.na le_rfl
  rcases tempToMainMemcpyTraced_post (.lo .finalTempToData)
    mergeLoFinalTempToDataPermit machine.na machine.state machine.dest
    (Int.ofNat machine.aPos) hmain hinvariant.tempActiveInBounds
    hinvariant.tempActiveValuesMode hinvariant.tempInvariant
    hinvariant.tempLive hinvariant.valuesMode with ⟨_, hpost⟩
  change (tempToMainMemcpyTraced? (.lo .finalTempToData)
    mergeLoFinalTempToDataPermit machine.na machine.state machine.dest
    (Int.ofNat machine.aPos)).trace.HasTempAccess .read
  exact hpost.tempReadEvent hna

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoCopyBTraced_hasTempRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoCopyBTraced_hasTempRead
  (origin : MergeState κ ν) (tempTotal : Nat) (endIndex : Int)
  (machine : MergeLoMachine κ ν)
  (hinvariant : MergeLoMachineInvariant origin tempTotal endIndex machine)
  (hna : machine.na = 1) (hnb : 0 < machine.nb) :
  (mergeLoCopyBTraced? machine).trace.HasTempAccess .read := by
  have hsrc := hinvariant.rightRange machine.nb le_rfl
  have hdst := hinvariant.destTotalRange machine.nb (by omega)
  rcases mainDataMemmoveTraced_safe machine.state machine.dest machine.bPos
    machine.nb hinvariant.tempInvariant hinvariant.tempLive
    hinvariant.valuesMode hdst hsrc with ⟨moved, hmove⟩
  rw [mergeLoCopyBTraced?, if_pos ⟨hna, hnb⟩]
  exact hasTempAccess_bind_right _ _ moved .read hmove.success
    (by
      change (tempToMainCellTraced? moved
        (machine.dest + Int.ofNat machine.nb)
        (Int.ofNat machine.aPos)).trace.HasTempAccess .read
      exact tempToMainCellTraced_hasTempRead moved
        (machine.dest + Int.ofNat machine.nb) (Int.ofNat machine.aPos))

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoOrdinaryLoopTraced_hasTempRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoOrdinaryLoopTraced_hasTempRead
  (fuel : Nat) (machine : MergeLoMachine κ ν)
  (hna : 1 < machine.na) (hnb : 0 < machine.nb) :
  (mergeLoLoopTraced? (fuel + 1) machine (.ordinary 0 0)).trace.HasTempAccess
    .read := by
  have hguard : ¬ (machine.na ≤ 1 ∨ machine.nb = 0) := by omega
  rw [mergeLoLoopTraced?, if_neg hguard]
  exact hasTempAccess_bind_left _ _ .read
    (tempPayloadRead_hasTempAccess machine.state.a (Int.ofNat machine.aPos))

end CPythonListsort

namespace CPythonListsort

/--
[mergeLo_prepareInitial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma mergeLo_prepareInitial
  {κ : Type u}
  {ν : Type v}
  {pre : MergeState κ ν}
  {scanned i : Nat}
  {call : MergeAtCall κ ν}
-- given
  (hlayout : PendingLayout pre scanned)
  (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
  (hprepare : prepareMergeAt? pre i = some (.mergeLo call))
  (hInv : TempStorageInv pre.a pre.alloced)
  (hLive : pre.a.Live)
  (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data) :
-- imply
  ∃ copied, MergeLoInitialStage pre scanned i call copied := by
-- proof
  have hrequest := mergeGetmem_lo_request_bound pre scanned i call hlayout hmax
    hprepare
  have hgeometry := mergeLo_callsite_safety_geometry pre scanned i call hlayout
    hmax hprepare
  have hevidence := hgeometry.evidence
  have hcallInv : TempStorageInv call.state.a call.state.alloced := by
    simpa only [hevidence.storage_eq, hevidence.alloced_eq] using hInv
  have hcallLive : call.state.a.Live := by
    simpa only [hevidence.storage_eq] using hLive
  have hcallMode :
    SortSlice.ValuesModeInvariant call.state.a.hasValues call.state.data := by
    simpa only [hevidence.hasValues_eq, hevidence.data_eq] using hMode
  have hallocPost : MergeGetmemStoragePost call.state
    (BitVec.ofNat 64 call.na) (mergeLoAllocated call) := by
    exact mergeGetmem_storage_valid call.state (BitVec.ofNat 64 call.na)
      hcallInv hcallLive hrequest.requestNonnegative
      (fun _ => hrequest.requestWithinLimit)
  have hallocatedMode :
    SortSlice.ValuesModeInvariant (mergeLoAllocated call).state.a.hasValues
      (mergeLoAllocated call).state.data := by
    simpa only [hallocPost.valuesMode, hallocPost.data_eq] using hcallMode
  have htempRange : TempRangeInBounds (mergeLoAllocated call).state.a 0
    call.na := by
    constructor
    · omega
    · simp only [zero_add]
      apply Int.ofNat_le.mpr
      rw [hallocPost.logicalCapacity]
      simpa only [hrequest.requestRoundtrip] using hallocPost.requestFits
  have hmainRange : SortSlice.RangeInBounds (mergeLoAllocated call).state.data
    call.ssa call.na := by
    constructor
    · exact hgeometry.ssaNonnegative
    · have hmerged := hgeometry.mergedRange
      rw [hallocPost.data_eq]
      simp only [Int.ofNat_eq_natCast, Nat.cast_add] at hmerged ⊢
      omega
  rcases mainToTempMemcpyTraced_post (.lo .initialDataToTemp)
    mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
    call.ssa htempRange hmainRange hallocPost.invariant hallocPost.live
    hallocatedMode with ⟨copied, hcopy⟩
  refine ⟨copied,
    { requestFacts := hrequest
      geometry := hgeometry
      inputTempInvariant := hcallInv
      inputTempLive := hcallLive
      inputValuesMode := hcallMode
      allocationPost := hallocPost
      copyPost := hcopy
      initialInvariant := ?_ }⟩
  refine
    { destNonnegative := ?_
      tempAccounting := ?_
      adjacency := ?_
      rightAccounting := ?_
      mainEnd := ?_
      leftWordBound := ?_
      rightWordBound := ?_
      tempCapacity := ?_
      tempValuesMode := ?_
      tempInvariant := hcopy.tempInvariant
      tempLive := hcopy.tempLive
      valuesMode := hcopy.valuesMode
      stableFrame := MergeLoStableFrame.of_movement hcopy.frame
      storageFrame := MergeLoStorageFrame.of_movement hcopy.frame }
  · exact hgeometry.ssaNonnegative
  · simp [mergeLoInitialMachine]
  · simpa [mergeLoInitialMachine] using hgeometry.adjacent
  · rfl
  · change mergeLoEndIndex call ≤ Int.ofNat copied.data.entries.size
    rwa [hcopy.frame.dataSize, hallocPost.data_eq]
  · change call.na ≤ PY_LIST_MAX
    have hrun := hgeometry.runLengthBound
    omega
  · change call.nb ≤ PY_LIST_MAX
    have hrun := hgeometry.runLengthBound
    omega
  · change call.na ≤ copied.a.cells.size
    rw [hcopy.frame.tempSize, hallocPost.logicalCapacity]
    simpa only [hrequest.requestRoundtrip] using hallocPost.requestFits
  · simpa [mergeLoInitialMachine] using hcopy.tempValuesMode

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLo_runCore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
shapes: immediate success, `CopyB`, or the fuel-bounded lockstep loop. -/
private lemma mergeLo_runCore
  (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
  (copied : MergeState κ ν)
  (stage : MergeLoInitialStage pre scanned i call copied) :
  ∃ result, MergeLoCoreStage call copied result := by
  let initial := mergeLoInitialMachine call copied
  have hinitial : MergeLoMachineInvariant (mergeLoAllocated call).state call.na
    (mergeLoEndIndex call) initial := by
    simpa only [initial] using stage.initialInvariant
  rcases mergeLoCopyBIncrTraced_safe (mergeLoAllocated call).state call.na
    (mergeLoEndIndex call) initial hinitial stage.geometry.leftPositive
    stage.geometry.rightPositive with
    ⟨afterB, hafterBResult, hafterBSafe, hafterBInv, hafterBNa,
      hafterBNb⟩
  have htail : ∃ result,
    MergeLoCorePost (mergeLoAllocated call).state call.na
      (mergeLoTracedTail call afterB)
      (mergeLoReferenceTail call afterB) result ∧
    (mergeLoTracedTail call afterB).trace.HasTempAccess .read := by
    by_cases hnbZero : afterB.nb = 0
    · rcases mergeLoSucceedTraced_safe (mergeLoAllocated call).state call.na
      (mergeLoEndIndex call) afterB hafterBInv with ⟨result, hpost⟩
      refine ⟨result, ?_, ?_⟩
      · simpa [mergeLoTracedTail, mergeLoReferenceTail, hnbZero] using hpost
      · simpa [mergeLoTracedTail, hnbZero] using
        (mergeLoSucceedTraced_hasTempRead (mergeLoAllocated call).state call.na
          (mergeLoEndIndex call) afterB hafterBInv (by
            rw [hafterBNa]
            simpa [initial, mergeLoInitialMachine] using
              stage.geometry.leftPositive))
    · have hnbPositive : 0 < afterB.nb := Nat.pos_of_ne_zero hnbZero
      by_cases hnaOne : afterB.na = 1
      · rcases mergeLoCopyBTraced_safe (mergeLoAllocated call).state call.na
        (mergeLoEndIndex call) afterB hafterBInv hnaOne hnbPositive with
        ⟨result, hpost⟩
        refine ⟨result, ?_, ?_⟩
        · simpa [mergeLoTracedTail, mergeLoReferenceTail, hnbZero, hnaOne]
          using hpost
        · simpa [mergeLoTracedTail, hnbZero, hnaOne] using
          (mergeLoCopyBTraced_hasTempRead (mergeLoAllocated call).state call.na
            (mergeLoEndIndex call) afterB hafterBInv hnaOne hnbPositive)
      · have hnaPositive : 0 < afterB.na := by
        rw [hafterBNa]
        simpa [initial, mergeLoInitialMachine] using
          stage.geometry.leftPositive
        have hnaLarge : 1 < afterB.na := by omega
        have hfuel : MergeLoFuelInvariant (call.na + call.nb + 1) afterB := by
          unfold MergeLoFuelInvariant
          rw [hafterBNa, hafterBNb]
          simp only [initial, mergeLoInitialMachine]
          omega
        rcases mergeLoLoopTraced_safe (mergeLoAllocated call).state call.na
          (mergeLoEndIndex call) (call.na + call.nb + 1) afterB
          (.ordinary 0 0) hafterBInv hfuel hnaLarge hnbPositive with
          ⟨result, hpost⟩
        refine ⟨result, ?_, ?_⟩
        · simpa [mergeLoTracedTail, mergeLoReferenceTail, hnbZero, hnaOne]
          using hpost
        · simpa [mergeLoTracedTail, hnbZero, hnaOne, Nat.add_assoc] using
          (mergeLoOrdinaryLoopTraced_hasTempRead (call.na + call.nb) afterB
            hnaLarge hnbPositive)
  obtain ⟨result, htailPost, htailRead⟩ := htail
  have hafterInitialRead :
    ((mergeLoCopyBIncrTraced? initial).bind
      (mergeLoTracedTail call)).trace.HasTempAccess .read :=
    hasTempAccess_bind_right (mergeLoCopyBIncrTraced? initial)
      (mergeLoTracedTail call) afterB .read hafterBResult htailRead
  have hafterInitial := MergeLoCorePost.prepend
    (mergeLoAllocated call).state call.na
    (mergeLoCopyBIncrTraced? initial) (mergeLoTracedTail call)
    (mergeLoReferenceTail call) afterB result hafterBResult hafterBSafe htailPost
  refine ⟨result, ?_⟩
  constructor
  · simpa [mergeLoTracedAfterCopy, mergeLoReferenceAfterCopy, initial] using
    hafterInitial
  · simpa [mergeLoTracedAfterCopy, initial] using hafterInitialRead

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLo_finish](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
the externally consumable trace, erasure, frame, storage, and provenance
witnesses. -/
private lemma mergeLo_finish
  (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν)
  (copied : MergeState κ ν)
  (stage : MergeLoInitialStage pre scanned i call copied)
  (result : MergeLoResult κ ν)
  (core : MergeLoCoreStage call copied result) :
  MergeLoSafetyPost pre scanned i call
    (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb) result := by
  have hwhole := MergeLoCorePost.prepend (mergeLoAllocated call).state call.na
    (mainToTempMemcpyTraced? (.lo .initialDataToTemp)
      mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
      call.ssa)
    (mergeLoTracedAfterCopy call) (mergeLoReferenceAfterCopy call)
    copied result stage.copyPost.success stage.copyPost.traceSafe
    core.corePost
  have hreference :
    (mainToTempMemcpyTraced? (.lo .initialDataToTemp)
      mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
      call.ssa).erase.bind (mergeLoReferenceAfterCopy call) =
      (mergeLoMemcpyDataToTemp? .initialDataToTemp rfl call.na
        (mergeLoAllocated call).state 0 call.ssa).bind
          (mergeLoReferenceAfterCopy call) := by
    calc
      _ = (mainToTempMemcpy? call.na (mergeLoAllocated call).state 0
        call.ssa).bind (mergeLoReferenceAfterCopy call) :=
        congrArg (fun option => option.bind (mergeLoReferenceAfterCopy call))
          stage.copyPost.exactErasure
      _ = _ := congrArg
        (fun option => option.bind (mergeLoReferenceAfterCopy call))
        (mainToTempMemcpy_eq_mergeLo .initialDataToTemp rfl call.na
          (mergeLoAllocated call).state 0 call.ssa)
  have hwholeTagged := MergeLoCorePost.reference_eq
    (mergeLoAllocated call).state call.na _ _ _ result hreference hwhole
  have hentryGuard :
    0 < call.na ∧ 0 < call.nb ∧ call.na ≤ PY_SSIZE_T_MAX ∧
      call.nb ≤ PY_SSIZE_T_MAX ∧
      call.ssa + Int.ofNat call.na = call.ssb :=
    ⟨stage.geometry.leftPositive, stage.geometry.rightPositive,
      stage.geometry.leftWordBound, stage.geometry.rightWordBound,
      stage.geometry.adjacent⟩
  have hcore : MergeLoCorePost (mergeLoAllocated call).state call.na
    (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb)
    (mergeLo? call.state call.ssa call.ssb call.na call.nb) result := by
    rw [mergeLoTraced?, if_pos hentryGuard,
      if_neg stage.requestFacts.guardNotRejected]
    rw [mergeLo?, if_pos hentryGuard,
      if_neg stage.requestFacts.guardNotRejected]
    change MergeLoCorePost (mergeLoAllocated call).state call.na
      ((mainToTempMemcpyTraced? (.lo .initialDataToTemp)
        mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
        call.ssa).bind (mergeLoTracedAfterCopy call))
      ((mergeLoMemcpyDataToTemp? .initialDataToTemp rfl call.na
        (mergeLoAllocated call).state 0 call.ssa).bind
          (mergeLoReferenceAfterCopy call)) result
    exact hwholeTagged
  have hinputEvent :
    (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb).trace.HasAccess
      .read .inputKeys := by
    have hprefixed := hasAccess_bind_left
      (mainToTempMemcpyTraced? (.lo .initialDataToTemp)
        mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
        call.ssa)
      (mergeLoTracedAfterCopy call) .read .inputKeys
      (stage.copyPost.inputKeyEvent stage.geometry.leftPositive)
    rw [mergeLoTraced?, if_pos hentryGuard,
      if_neg stage.requestFacts.guardNotRejected]
    change ((mainToTempMemcpyTraced? (.lo .initialDataToTemp)
      mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
      call.ssa).bind (mergeLoTracedAfterCopy call)).trace.HasAccess
        .read .inputKeys
    exact hprefixed
  have htempWriteEvent :
    (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb).trace.HasTempAccess
      .write := by
    have hprefixed := hasTempAccess_bind_left
      (mainToTempMemcpyTraced? (.lo .initialDataToTemp)
        mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
        call.ssa)
      (mergeLoTracedAfterCopy call) .write
      (stage.copyPost.tempWriteEvent stage.geometry.leftPositive)
    rw [mergeLoTraced?, if_pos hentryGuard,
      if_neg stage.requestFacts.guardNotRejected]
    change ((mainToTempMemcpyTraced? (.lo .initialDataToTemp)
      mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
      call.ssa).bind (mergeLoTracedAfterCopy call)).trace.HasTempAccess .write
    exact hprefixed
  have htempReadEvent :
    (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb).trace.HasTempAccess
      .read := by
    have hprefixed := hasTempAccess_bind_right
      (mainToTempMemcpyTraced? (.lo .initialDataToTemp)
        mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
        call.ssa)
      (mergeLoTracedAfterCopy call) copied .read
      stage.copyPost.success core.tempRead
    rw [mergeLoTraced?, if_pos hentryGuard,
      if_neg stage.requestFacts.guardNotRejected]
    change ((mainToTempMemcpyTraced? (.lo .initialDataToTemp)
      mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
      call.ssa).bind (mergeLoTracedAfterCopy call)).trace.HasTempAccess .read
    exact hprefixed
  have hlogical := TempStorageInv.cells_size_eq hcore.tempInvariant hcore.tempLive
  have hphysicalBound :
    call.state.a.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES →
      result.state.a.physicalSlots ≤
        PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
    intro hbefore
    rw [hcore.storageFrame.physicalSlots_eq]
    obtain hreuse | hgrown := stage.allocationPost.outcome
    · rw [stage.allocationPost.reuseAccounting hreuse]
      exact hbefore
    · exact (stage.allocationPost.growthAccounting hgrown).2.2.2.2
  refine
    { resultEq := hcore.resultEq
      returnCode := hcore.returnCode
      resultFuel := hcore.resultFuel
      traceFuel := hcore.traceSafe.fuel
      accessesInBounds := hcore.traceSafe.bounds
      tempAccessesLive := hcore.traceSafe.tempLive
      noPushes := hcore.traceSafe.noPushes
      noMemoryEvents := mergeLoTraced_memoryEvents_empty
        call.state call.ssa call.ssb call.na call.nb
      exactErasure := hcore.exactErasure
      tempInvariant := hcore.tempInvariant
      tempLive := hcore.tempLive
      logicalCapacity := hlogical
      requestFits := hcore.tempCapacity.trans_eq hlogical
      valuesMode := hcore.valuesMode
      stableFrame := (MergeLoStableFrame.of_getmem call.state
        (BitVec.ofNat 64 call.na) stage.allocationPost).trans hcore.stableFrame
      geometry := stage.geometry
      requestFacts := stage.requestFacts
      inputTempInvariant := stage.inputTempInvariant
      inputTempLive := stage.inputTempLive
      inputValuesMode := stage.inputValuesMode
      allocationPost := stage.allocationPost
      postGetmemStorageFrame := hcore.storageFrame
      physicalSlotsBound := hphysicalBound
      memcpyProvenance := stage.copyPost.provenanceContract
      inputKeyEvent := hinputEvent
      tempWriteEvent := htempWriteEvent
      tempReadEvent := htempReadEvent
      synchronizedValuesEvent := ?_ }
  intro hvalues
  have hallocatedValues : (mergeLoAllocated call).state.a.hasValues = true :=
    stage.allocationPost.valuesMode.trans hvalues
  have hprefixed := hasAccess_bind_left
    (mainToTempMemcpyTraced? (.lo .initialDataToTemp)
      mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
      call.ssa)
    (mergeLoTracedAfterCopy call) .read .synchronizedValues
    (stage.copyPost.synchronizedValuesEvent stage.geometry.leftPositive
      hallocatedValues)
  rw [mergeLoTraced?, if_pos hentryGuard,
    if_neg stage.requestFacts.guardNotRejected]
  change ((mainToTempMemcpyTraced? (.lo .initialDataToTemp)
    mergeLoInitialDataToTempPermit call.na (mergeLoAllocated call).state 0
    call.ssa).bind (mergeLoTracedAfterCopy call)).trace.HasAccess
      .read .synchronizedValues
  exact hprefixed

end CPythonListsort

namespace CPythonListsort

/--
[mergeLo_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma mergeLo_safe
  {κ : Type u}
  {ν : Type v}
  {pre : MergeState κ ν}
  {scanned i : Nat}
  {call : MergeAtCall κ ν}
-- given
  (hlayout : PendingLayout pre scanned)
  (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
  (hprepare : prepareMergeAt? pre i = some (.mergeLo call))
  (hInv : TempStorageInv pre.a pre.alloced)
  (hLive : pre.a.Live)
  (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data) :
-- imply
  ∃ result, MergeLoSafetyPost pre scanned i call (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb) result := by
-- proof
  let stage := mergeLo_prepareInitial pre scanned i call hlayout hmax hprepare
    hInv hLive hMode
  obtain ⟨copied, stage⟩ := stage
  obtain ⟨result, core⟩ := mergeLo_runCore pre scanned i call copied stage
  exact ⟨result, mergeLo_finish pre scanned i call copied stage result core⟩

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeLoGallopTempToDataTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma erase_mergeLoGallopTempToDataTraced
  {κ : Type u}
  {ν : Type v}
  {count : Nat}
  {state : MergeState κ ν}
  {destination : Int}
  {source : Nat} :
-- imply
  (tempToMainMemcpyTraced? (.lo .gallopTempToData) mergeLoGallopTempToDataPermit count state destination (Int.ofNat source)).erase = mergeLoMemcpyTempToData? .gallopTempToData rfl count state destination source := by
-- proof
  calc
    _ = tempToMainMemcpy? count state destination (Int.ofNat source) :=
      erase_tempToMainMemcpyTraced (.lo .gallopTempToData)
        mergeLoGallopTempToDataPermit count state destination
        (Int.ofNat source)
    _ = _ := tempToMainMemcpy_eq_mergeLo .gallopTempToData rfl count state
      destination source

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeLoInitialDataToTempTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma erase_mergeLoInitialDataToTempTraced
  {κ : Type u}
  {ν : Type v}
  {count : Nat}
  {state : MergeState κ ν}
  {destination : Nat}
  {source : Int} :
-- imply
  (mainToTempMemcpyTraced? (.lo .initialDataToTemp) mergeLoInitialDataToTempPermit count state (Int.ofNat destination) source).erase = mergeLoMemcpyDataToTemp? .initialDataToTemp rfl count state destination source := by
-- proof
  calc
    _ = mainToTempMemcpy? count state (Int.ofNat destination) source :=
      erase_mainToTempMemcpyTraced (.lo .initialDataToTemp)
        mergeLoInitialDataToTempPermit count state (Int.ofNat destination)
        source
    _ = _ := mainToTempMemcpy_eq_mergeLo .initialDataToTemp rfl count state
      destination source

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeLoTemporaryGallopRightRaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma erase_mergeLoTemporaryGallopRightRaw
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {start count : Nat}
  {slice : SortSlice κ ν}
  {key : κ}
-- given
  (hslice : mergeLoTempRun? state.a start count = some slice) :
-- imply
  (gallopRightTraced? state (.temporary state.a (Int.ofNat start)) key count 0).erase = gallopRight? state slice 0 key count 0 := by
-- proof
  rw [erase_gallopRightTraced]
  by_cases hinput : 0 < count ∧ count ≤ PY_SSIZE_T_MAX
  · exact gallopRightFromSource_eq_slice_of_ssize state
    (.temporary state.a (Int.ofNat start)) slice 0 key count 0
    (tempRun_agreesWithSlice_of_eq_some state.a start count slice hslice)
    hinput.1 (by omega) hinput.2
  · unfold gallopRightFromSource? gallopRight?
    have hguard : ¬(0 < count ∧ 0 < count ∧ count ≤ PY_SSIZE_T_MAX) := by
      aesop
    simp only [hguard, if_false]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[traceErase_bind_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma traceErase_bind_reachable
  {α β : Type*}
  (traced : TraceResult α) (raw : Option α)
  (nextTraced : α → TraceResult β) (next : α → Option β)
  (hsource : traced.erase = raw)
  (hnext : ∀ value, raw = some value →
    (nextTraced value).erase = next value) :
  (traced.bind nextTraced).erase = raw.bind next := by
  rw [TraceResult.erase_bind, hsource]
  cases hraw : raw with
  | none => simp
  | some value => simpa [hraw] using hnext value hraw

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[traceErase_bindAcross_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma traceErase_bindAcross_reachable
  {α β : Type*}
  (traced : TraceResult α) (raw : Option α)
  (nextTraced : α → TraceResult β) (next : α → Option β)
  (hsource : traced.erase = raw)
  (hnext : ∀ value, raw = some value →
    (nextTraced value).erase = next value) :
  (traced.bind nextTraced).erase = mergeLoBindOptionAcross raw next := by
  unfold mergeLoBindOptionAcross
  rw [TraceResult.erase_bind, hsource]
  cases hraw : raw with
  | none => rfl
  | some value => simpa [hraw] using hnext value hraw

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mainDataMemmove_bind_eq_raw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mainDataMemmove_bind_eq_raw
  (state : MergeState κ ν) (dst src : Int) (count : Nat)
  (next : MergeState κ ν → Option α) :
  (mainDataMemmove? state dst src count).bind next =
    (state.data.memmove? dst src count).bind fun data =>
      next { state with data := data } := by
  unfold mainDataMemmove?
  cases state.data.memmove? dst src count <;> rfl

end CPythonListsort

namespace CPythonListsort

/--
[erase_mergeLoGallopRoundTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
lemma erase_mergeLoGallopRoundTraced
  {κ : Type u}
  {ν : Type v}
  {machine : MergeLoMachine κ ν}
  {nextTraced : MergeLoMachine κ ν → Nat → Nat → TraceResult (MergeLoResult κ ν)}
  {next : MergeLoMachine κ ν → Nat → Nat → Option (MergeLoResult κ ν)}
-- given
  (hnext : ∀ machine aCount bCount, (nextTraced machine aCount bCount).erase = next machine aCount bCount) :
-- imply
  (mergeLoGallopRoundTraced? machine nextTraced).erase = mergeLoGallopRound? machine next := by
-- proof
  unfold mergeLoGallopRoundTraced? mergeLoGallopRound?
  split
  · rfl
  · let minGallop :=
    if (1 : PySSize).slt machine.minGallop then
      machine.minGallop - 1
    else machine.minGallop
    let adjustedState := { machine.state with min_gallop := minGallop }
    let adjusted : MergeLoMachine κ ν :=
      { machine with state := adjustedState, minGallop := minGallop }
    apply traceErase_bind_reachable
      (TraceResult.sortSliceKeysRead? adjusted.state.data adjusted.bPos)
      (adjusted.state.data.read? adjusted.bPos)
      _ _ (TraceResult.erase_sortSliceKeysRead _ _)
    intro firstB _
    apply traceErase_bind_reachable
      (mergeLoTraceOption
        (mergeLoTempRun? adjusted.state.a adjusted.aPos adjusted.na))
      (mergeLoTempRun? adjusted.state.a adjusted.aPos adjusted.na)
      _ _ (mergeLoTraceOption_erase _)
    intro activeA hactive
    dsimp [adjusted, adjustedState, minGallop] at hactive ⊢
    apply traceErase_bindAcross_reachable
      (gallopRightTraced?
        { machine.state with
          min_gallop := if (1 : PySSize).slt machine.minGallop then
            machine.minGallop - 1 else machine.minGallop }
        (.temporary machine.state.a (Int.ofNat machine.aPos))
        firstB.key machine.na 0)
      (gallopRight?
        { machine.state with
          min_gallop := if (1 : PySSize).slt machine.minGallop then
            machine.minGallop - 1 else machine.minGallop }
        activeA 0 firstB.key machine.na 0)
      _ _ (erase_mergeLoTemporaryGallopRightRaw
        { machine.state with
          min_gallop := if (1 : PySSize).slt machine.minGallop then
            machine.minGallop - 1 else machine.minGallop }
        machine.aPos machine.na activeA firstB.key hactive)
    intro gallopA _
    by_cases hfuel : gallopA.fuelExhausted = true
    · simp only [hfuel, if_true]
      exact erase_mergeLoFuelFailureTraced _
    · simp only [hfuel]
      by_cases hover : gallopA.index > machine.na
      · simp only [hover, if_true]
        rfl
      · simp only [hover, if_false]
        apply traceErase_bind_reachable
          (tempToMainMemcpyTraced? (.lo .gallopTempToData)
            mergeLoGallopTempToDataPermit gallopA.index
            { machine.state with
              min_gallop := if (1 : PySSize).slt machine.minGallop then
                machine.minGallop - 1 else machine.minGallop }
            machine.dest (Int.ofNat machine.aPos))
          (mergeLoMemcpyTempToData? .gallopTempToData rfl gallopA.index
            { machine.state with
              min_gallop := if (1 : PySSize).slt machine.minGallop then
                machine.minGallop - 1 else machine.minGallop }
            machine.dest machine.aPos)
          _ _ (erase_mergeLoGallopTempToDataTraced gallopA.index
            { machine.state with
              min_gallop := if (1 : PySSize).slt machine.minGallop then
                machine.minGallop - 1 else machine.minGallop }
            machine.dest machine.aPos)
        intro state _
        by_cases hna0 : machine.na - gallopA.index = 0
        · simp only [hna0, if_true]
          exact erase_mergeLoSucceedTraced _
        · simp only [hna0, if_false]
          by_cases hna1 : machine.na - gallopA.index = 1
          · simp only [hna1, if_true]
            exact erase_mergeLoCopyBTraced _
          · simp only [hna1, if_false]
            apply traceErase_bind_reachable
              (mergeLoCopyBIncrTraced? _)
              (mergeLoCopyBIncr? _)
              _ _ (erase_mergeLoCopyBIncrTraced _)
            intro afterB _
            by_cases hnb0 : afterB.nb = 0
            · simp only [hnb0, if_true]
              exact erase_mergeLoSucceedTraced _
            · simp only [hnb0, if_false]
              apply traceErase_bind_reachable
                (TraceResult.tempPayloadRead? afterB.state.a
                  (Int.ofNat afterB.aPos))
                (mergeLoTempRead? afterB.state.a afterB.aPos)
                _ _ ((TraceResult.erase_tempPayloadRead _ _).trans
                  (mergeTempRead_ofNat _ _))
              intro firstA _
              apply traceErase_bindAcross_reachable
                (gallopLeftTraced? afterB.state
                  (.main afterB.state.data afterB.bPos)
                  firstA.key afterB.nb 0)
                (gallopLeft? afterB.state afterB.state.data afterB.bPos
                  firstA.key afterB.nb 0)
                _ _ (erase_gallopLeftTraced_main _ _ _ _ _ _)
              intro gallopB _
              by_cases hbfuel : gallopB.fuelExhausted = true
              · simp only [hbfuel, if_true]
                exact erase_mergeLoFuelFailureTraced _
              · simp only [hbfuel]
                by_cases hbindex : gallopB.index > afterB.nb
                · simp only [hbindex, if_true]
                  rfl
                · simp only [hbindex, if_false]
                  simp only [Bool.false_eq_true, if_false]
                  let rawAfterMove (movedB : MergeState κ ν) :
                    Option (MergeLoResult κ ν) :=
                    let nextMachine : MergeLoMachine κ ν :=
                      { afterB with
                        state := movedB
                        dest := afterB.dest + Int.ofNat gallopB.index
                        bPos := afterB.bPos + Int.ofNat gallopB.index
                        nb := afterB.nb - gallopB.index }
                    if nextMachine.nb = 0 then
                      mergeLoSucceed? nextMachine
                    else do
                      let nextMachine ← mergeLoCopyAIncr? nextMachine
                      if nextMachine.na = 1 then
                        mergeLoCopyB? nextMachine
                      else
                        next nextMachine gallopA.index gallopB.index
                  change _ =
                    (afterB.state.data.memmove? afterB.dest afterB.bPos
                      gallopB.index).bind fun data =>
                        rawAfterMove { afterB.state with data := data }
                  rw [← mainDataMemmove_bind_eq_raw
                    afterB.state afterB.dest afterB.bPos gallopB.index
                    rawAfterMove]
                  apply traceErase_bind_reachable
                    (mainDataMemmoveTraced? afterB.state afterB.dest afterB.bPos
                      gallopB.index)
                    (mainDataMemmove? afterB.state afterB.dest afterB.bPos
                      gallopB.index)
                    _ _ (erase_mainDataMemmoveTraced _ _ _ _)
                  intro movedB _
                  dsimp [rawAfterMove]
                  by_cases hnbDone : afterB.nb - gallopB.index = 0
                  · simp only [hnbDone, if_true]
                    exact erase_mergeLoSucceedTraced _
                  · simp only [hnbDone, if_false]
                    apply traceErase_bind_reachable
                      (mergeLoCopyAIncrTraced? _)
                      (mergeLoCopyAIncr? _)
                      _ _ (erase_mergeLoCopyAIncrTraced _)
                    intro afterA _
                    by_cases hnaDone : afterA.na = 1
                    · simp only [hnaDone, if_true]
                      exact erase_mergeLoCopyBTraced _
                    · simp only [hnaDone, if_false]
                      exact hnext _ _ _

end CPythonListsort

/--
[mergeLoInitialDataToTempPermit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoInitialDataToTempPermit_eq
  {κ : Type u}
  {ν : Type v} :
-- imply
  (MergeMemcpySite.lo .initialDataToTemp).MainToTempPermit where direction := by
-- proof
  apply CPythonListsort.mergeLoInitialDataToTempPermit

/--
[mergeLoGallopTempToDataPermit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoGallopTempToDataPermit_eq
  {κ : Type u}
  {ν : Type v} :
-- imply
  (MergeMemcpySite.lo .gallopTempToData).TempToMainPermit where direction := by
-- proof
  apply CPythonListsort.mergeLoGallopTempToDataPermit

/--
[mergeLoFinalTempToDataPermit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeLoSafety.lean)
-/
@[path]
private lemma mergeLoFinalTempToDataPermit_eq
  {κ : Type u}
  {ν : Type v} :
-- imply
  (MergeMemcpySite.lo .finalTempToData).TempToMainPermit where direction := by
-- proof
  apply CPythonListsort.mergeLoFinalTempToDataPermit


-- created on 2026-10-23

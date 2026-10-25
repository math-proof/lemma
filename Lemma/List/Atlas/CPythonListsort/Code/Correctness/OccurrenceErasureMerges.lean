import Mathlib
import sympy.Basic
import Theorem.CPythonListsort.Code.Correctness.OccurrenceErasureMerges.Part2
open CPythonListsort


namespace CPythonListsort

/--
[eraseOccurrenceMergeDataMemmove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeDataMemmove
  {alpha : Type u}
  {nu : Type v}
  {site : MergeMemmoveCallsite}
  {data : SortSlice (Occurrence alpha) nu}
  {dst src : Int}
  {count : Nat} :
-- imply
  mergeDataMemmove? site (eraseOccurrenceSlice data) dst src count = (mergeDataMemmove? site data dst src count).map (eraseOccurrenceSlice) := by
-- proof
  simp [mergeDataMemmove?]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoTempRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoTempRead
  {alpha : Type u}
  {nu : Type v}
  {storage : TempStorage (Occurrence alpha) nu}
  {index : Nat} :
-- imply
  mergeLoTempRead? (eraseOccurrenceTempStorage storage) index = (mergeLoTempRead? storage index).map (eraseOccurrenceEntry) := by
-- proof
  cases hcell : storage.cells[index]? with
  | none => simp [mergeLoTempRead?, eraseOccurrenceTempStorage, hcell]
  | some cell =>
    cases cell <;> simp [mergeLoTempRead?, eraseOccurrenceTempStorage, hcell]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoTempWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoTempWrite
  {alpha : Type u}
  {nu : Type v}
  {storage : TempStorage (Occurrence alpha) nu}
  {index : Nat}
  {entry : SortSliceEntry (Occurrence alpha) nu} :
-- imply
  mergeLoTempWrite? (eraseOccurrenceTempStorage storage) index (eraseOccurrenceEntry entry) = (mergeLoTempWrite? storage index entry).map (eraseOccurrenceTempStorage) := by
-- proof
  unfold mergeLoTempWrite?
  simp only [eraseOccurrenceTempStorage_cells_size]
  split
  · simp [eraseOccurrenceTempStorage, Array.map_set]
  · rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoMemcpyDataToTemp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoMemcpyDataToTemp
  {alpha : Type u}
  {nu : Type v}
  {site : MergeLoMemcpyCallsite}
  {count : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {destination : Nat}
  {source : Int}
-- given
  (hDirection : site.backings = { destination := .temporary, source := .main }) :
-- imply
  mergeLoMemcpyDataToTemp? site hDirection count (eraseOccurrenceMergeState state) destination source = (mergeLoMemcpyDataToTemp? site hDirection count state destination source).map (eraseOccurrenceMergeState) := by
-- proof
  induction count generalizing state destination source with
  | zero => rfl
  | succ count ih =>
    simp only [mergeLoMemcpyDataToTemp?]
    simp only [eraseOccurrenceMergeState_data, eraseOccurrenceMergeState_tempStorage,
      eraseOccurrenceMergeState_minGallop, eraseOccurrenceMergeState_listlen,
      eraseOccurrenceMergeState_basekeys, eraseOccurrenceMergeState_alloced,
      eraseOccurrenceMergeState_pending, eraseOccurrenceMergeState_key_compare,
      eraseOccurrenceMergeState_mrCurrent, eraseOccurrenceMergeState_mrE,
      eraseOccurrenceMergeState_mrMask]
    rw [eraseOccurrenceSlice_read]
    cases hread : state.data.read? source with
    | none => rfl
    | some entry =>
      simp only [Option.map_some, bind, Option.bind]
      rw [eraseOccurrenceMergeLoTempWrite]
      cases hwrite : mergeLoTempWrite? state.a destination entry with
      | none => rfl
      | some storage =>
        simp only [Option.map_some]
        simpa [eraseOccurrenceMergeState] using
          ih (state := { state with a := storage })
            (destination := destination + 1) (source := source + 1)

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoMemcpyTempToData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoMemcpyTempToData
  {alpha : Type u}
  {nu : Type v}
  {site : MergeLoMemcpyCallsite}
  {count : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {destination : Int}
  {source : Nat}
-- given
  (hDirection : site.backings = { destination := .main, source := .temporary }) :
-- imply
  mergeLoMemcpyTempToData? site hDirection count (eraseOccurrenceMergeState state) destination source = (mergeLoMemcpyTempToData? site hDirection count state destination source).map (eraseOccurrenceMergeState) := by
-- proof
  induction count generalizing state destination source with
  | zero => rfl
  | succ count ih =>
    simp only [mergeLoMemcpyTempToData?]
    simp only [eraseOccurrenceMergeState_data, eraseOccurrenceMergeState_tempStorage,
      eraseOccurrenceMergeState_minGallop, eraseOccurrenceMergeState_listlen,
      eraseOccurrenceMergeState_basekeys, eraseOccurrenceMergeState_alloced,
      eraseOccurrenceMergeState_pending, eraseOccurrenceMergeState_key_compare,
      eraseOccurrenceMergeState_mrCurrent, eraseOccurrenceMergeState_mrE,
      eraseOccurrenceMergeState_mrMask]
    rw [eraseOccurrenceMergeLoTempRead]
    cases hread : mergeLoTempRead? state.a source with
    | none => rfl
    | some entry =>
      simp only [Option.map_some, bind, Option.bind]
      rw [eraseOccurrenceSlice_write]
      cases hwrite : state.data.write? destination entry with
      | none => rfl
      | some data =>
        simp only [Option.map_some]
        simpa [eraseOccurrenceMergeState] using
          ih (state := { state with data := data })
            (destination := destination + 1) (source := source + 1)

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoInitialDataToTemp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoInitialDataToTemp
  {alpha : Type u}
  {nu : Type v}
  {count : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {destination : Nat}
  {source : Int} :
-- imply
  mergeLoMemcpyDataToTemp? .initialDataToTemp rfl count (eraseOccurrenceMergeState state) destination source = (mergeLoMemcpyDataToTemp? .initialDataToTemp rfl count state destination source).map (eraseOccurrenceMergeState) := by
-- proof
  exact eraseOccurrenceMergeLoMemcpyDataToTemp .initialDataToTemp rfl count state
    destination source

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoGallopTempToData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoGallopTempToData
  {alpha : Type u}
  {nu : Type v}
  {count : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {destination : Int}
  {source : Nat} :
-- imply
  mergeLoMemcpyTempToData? .gallopTempToData rfl count (eraseOccurrenceMergeState state) destination source = (mergeLoMemcpyTempToData? .gallopTempToData rfl count state destination source).map (eraseOccurrenceMergeState) := by
-- proof
  exact eraseOccurrenceMergeLoMemcpyTempToData .gallopTempToData rfl count state
    destination source

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoFinalTempToData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoFinalTempToData
  {alpha : Type u}
  {nu : Type v}
  {count : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {destination : Int}
  {source : Nat} :
-- imply
  mergeLoMemcpyTempToData? .finalTempToData rfl count (eraseOccurrenceMergeState state) destination source = (mergeLoMemcpyTempToData? .finalTempToData rfl count state destination source).map (eraseOccurrenceMergeState) := by
-- proof
  exact eraseOccurrenceMergeLoMemcpyTempToData .finalTempToData rfl count state
    destination source

end CPythonListsort

namespace CPythonListsort

/--
[occurrenceErasure_mergeLoMemcpyDataToTemp_key_compare_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma occurrenceErasure_mergeLoMemcpyDataToTemp_key_compare_of_eq_some
  {alpha : Type u}
  {nu : Type v}
  {site : MergeLoMemcpyCallsite}
  {count : Nat}
  {state result : MergeState κ ν}
  {destination : Nat}
  {source : Int}
-- given
  (hDirection : site.backings = { destination := .temporary, source := .main })
  (h : mergeLoMemcpyDataToTemp? site hDirection count state destination source = some result) :
-- imply
  result.key_compare = state.key_compare := by
-- proof
  induction count generalizing state destination source with
  | zero =>
    simp only [mergeLoMemcpyDataToTemp?] at h
    injection h with h
    subst result
    rfl
  | succ count ih =>
    simp only [mergeLoMemcpyDataToTemp?, bind, Option.bind] at h
    split at h <;> simp_all
    split at h <;> simp_all
    simpa using ih _ _ _ h

end CPythonListsort

namespace CPythonListsort

/--
[occurrenceErasure_mergeLoMemcpyTempToData_key_compare_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma occurrenceErasure_mergeLoMemcpyTempToData_key_compare_of_eq_some
  {alpha : Type u}
  {nu : Type v}
  {site : MergeLoMemcpyCallsite}
  {count : Nat}
  {state result : MergeState κ ν}
  {destination : Int}
  {source : Nat}
-- given
  (hDirection : site.backings = { destination := .main, source := .temporary })
  (h : mergeLoMemcpyTempToData? site hDirection count state destination source = some result) :
-- imply
  result.key_compare = state.key_compare := by
-- proof
  induction count generalizing state destination source with
  | zero =>
    simp only [mergeLoMemcpyTempToData?] at h
    injection h with h
    subst result
    rfl
  | succ count ih =>
    simp only [mergeLoMemcpyTempToData?, bind, Option.bind] at h
    split at h <;> simp_all
    split at h <;> simp_all
    simpa using ih _ _ _ h

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoGatherTempEntries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoGatherTempEntries
  {alpha : Type u}
  {nu : Type v}
  {count : Nat}
  {storage : TempStorage (Occurrence alpha) nu}
  {source : Nat}
  {entries : Array (SortSliceEntry (Occurrence alpha) nu)} :
-- imply
  mergeLoGatherTempEntries? count (eraseOccurrenceTempStorage storage) source (entries.map (eraseOccurrenceEntry)) = (mergeLoGatherTempEntries? count storage source entries).map (Array.map (eraseOccurrenceEntry)) := by
-- proof
  induction count generalizing source entries with
  | zero => rfl
  | succ count ih =>
    simp only [mergeLoGatherTempEntries?]
    rw [eraseOccurrenceMergeLoTempRead]
    cases hread : mergeLoTempRead? storage source with
    | none => rfl
    | some entry =>
      simp only [Option.map_some]
      simpa [Array.map_push] using
        ih (source := source + 1) (entries := entries.push entry)

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoTempRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoTempRun
  {alpha : Type u}
  {nu : Type v}
  {storage : TempStorage (Occurrence alpha) nu}
  {source count : Nat} :
-- imply
  mergeLoTempRun? (eraseOccurrenceTempStorage storage) source count = (mergeLoTempRun? storage source count).map (eraseOccurrenceSlice) := by
-- proof
  unfold mergeLoTempRun?
  have hgather :
    mergeLoGatherTempEntries? count (eraseOccurrenceTempStorage storage) source #[] =
      (mergeLoGatherTempEntries? count storage source #[]).map
        (Array.map (eraseOccurrenceEntry)) := by
    simpa using eraseOccurrenceMergeLoGatherTempEntries count storage source #[]
  rw [hgather]
  cases hentries : mergeLoGatherTempEntries? count storage source #[] with
  | none => rfl
  | some entries => simp [eraseOccurrenceSlice]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoResult_returnCode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoResult_returnCode
  {alpha : Type u}
  {nu : Type v}
  {result : MergeLoResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeLoResult result).returnCode = result.returnCode :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoResult_fuelExhausted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoResult_fuelExhausted
  {alpha : Type u}
  {nu : Type v}
  {result : MergeLoResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeLoResult result).fuelExhausted = result.fuelExhausted :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoMachine_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoMachine_state
  {alpha : Type u}
  {nu : Type v}
  {machine : MergeLoMachine (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeLoMachine machine).state = eraseOccurrenceMergeState machine.state :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoMachine_dest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoMachine_dest
  {alpha : Type u}
  {nu : Type v}
  {machine : MergeLoMachine (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeLoMachine machine).dest = machine.dest :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoMachine_aPos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoMachine_aPos
  {alpha : Type u}
  {nu : Type v}
  {machine : MergeLoMachine (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeLoMachine machine).aPos = machine.aPos :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoMachine_bPos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoMachine_bPos
  {alpha : Type u}
  {nu : Type v}
  {machine : MergeLoMachine (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeLoMachine machine).bPos = machine.bPos :=
-- proof
  rfl
@[simp] theorem eraseOccurrenceMergeLoMachine_na (machine : MergeLoMachine (Occurrence alpha) nu) :
  (eraseOccurrenceMergeLoMachine machine).na = machine.na := rfl
@[simp] theorem eraseOccurrenceMergeLoMachine_nb (machine : MergeLoMachine (Occurrence alpha) nu) :
  (eraseOccurrenceMergeLoMachine machine).nb = machine.nb := rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoMachine_minGallop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoMachine_minGallop
  {alpha : Type u}
  {nu : Type v}
  {machine : MergeLoMachine (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeLoMachine machine).minGallop = machine.minGallop :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoFailure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoFailure
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  mergeLoFailure (eraseOccurrenceMergeState state) = eraseOccurrenceMergeLoResult (mergeLoFailure state) :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoOutOfFuel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoOutOfFuel
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  mergeLoOutOfFuel (eraseOccurrenceMergeState state) = eraseOccurrenceMergeLoResult (mergeLoOutOfFuel state) :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoSuccess](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoSuccess
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  mergeLoSuccess (eraseOccurrenceMergeState state) = eraseOccurrenceMergeLoResult (mergeLoSuccess state) :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoCopyAIncr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoCopyAIncr
  {alpha : Type u}
  {nu : Type v}
  {machine : MergeLoMachine (Occurrence alpha) nu} :
-- imply
  mergeLoCopyAIncr? (eraseOccurrenceMergeLoMachine machine) = (mergeLoCopyAIncr? machine).map (eraseOccurrenceMergeLoMachine) := by
-- proof
  unfold mergeLoCopyAIncr?
  simp only [eraseOccurrenceMergeLoMachine_state, eraseOccurrenceMergeLoMachine_aPos,
    eraseOccurrenceMergeLoMachine_dest, eraseOccurrenceMergeLoMachine_bPos,
    eraseOccurrenceMergeLoMachine_na, eraseOccurrenceMergeLoMachine_nb,
    eraseOccurrenceMergeLoMachine_minGallop, eraseOccurrenceMergeState_tempStorage,
    eraseOccurrenceMergeState_data]
  rw [eraseOccurrenceMergeLoTempRead]
  cases hread : mergeLoTempRead? machine.state.a machine.aPos with
  | none => rfl
  | some entry =>
    simp only [Option.map_some, bind, Option.bind]
    rw [eraseOccurrenceSlice_write]
    cases hwrite : machine.state.data.write? machine.dest entry with
    | none => rfl
    | some data => simp [eraseOccurrenceMergeLoMachine, eraseOccurrenceMergeState]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoCopyBIncr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoCopyBIncr
  {alpha : Type u}
  {nu : Type v}
  {machine : MergeLoMachine (Occurrence alpha) nu} :
-- imply
  mergeLoCopyBIncr? (eraseOccurrenceMergeLoMachine machine) = (mergeLoCopyBIncr? machine).map (eraseOccurrenceMergeLoMachine) := by
-- proof
  unfold mergeLoCopyBIncr?
  simp only [eraseOccurrenceMergeLoMachine_state, eraseOccurrenceMergeLoMachine_aPos,
    eraseOccurrenceMergeLoMachine_dest, eraseOccurrenceMergeLoMachine_bPos,
    eraseOccurrenceMergeLoMachine_na, eraseOccurrenceMergeLoMachine_nb,
    eraseOccurrenceMergeLoMachine_minGallop, eraseOccurrenceMergeState_tempStorage,
    eraseOccurrenceMergeState_data]
  rw [eraseOccurrenceSlice_read]
  cases hread : machine.state.data.read? machine.bPos with
  | none => rfl
  | some entry =>
    simp only [Option.map_some, bind, Option.bind]
    rw [eraseOccurrenceSlice_write]
    cases hwrite : machine.state.data.write? machine.dest entry with
    | none => rfl
    | some data => simp [eraseOccurrenceMergeLoMachine, eraseOccurrenceMergeState]

end CPythonListsort

namespace CPythonListsort

/--
[occurrenceErasure_mergeLoCopyAIncr_key_compare_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma occurrenceErasure_mergeLoCopyAIncr_key_compare_of_eq_some
  {alpha : Type u}
  {nu : Type v}
  {machine result : MergeLoMachine κ ν}
-- given
  (h : mergeLoCopyAIncr? machine = some result) :
-- imply
  result.state.key_compare = machine.state.key_compare := by
-- proof
  simp only [mergeLoCopyAIncr?, bind, Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  subst result
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[occurrenceErasure_mergeLoCopyBIncr_key_compare_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma occurrenceErasure_mergeLoCopyBIncr_key_compare_of_eq_some
  {alpha : Type u}
  {nu : Type v}
  {machine result : MergeLoMachine κ ν}
-- given
  (h : mergeLoCopyBIncr? machine = some result) :
-- imply
  result.state.key_compare = machine.state.key_compare := by
-- proof
  simp only [mergeLoCopyBIncr?, bind, Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  subst result
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoSucceed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoSucceed
  {alpha : Type u}
  {nu : Type v}
  {machine : MergeLoMachine (Occurrence alpha) nu} :
-- imply
  mergeLoSucceed? (eraseOccurrenceMergeLoMachine machine) = (mergeLoSucceed? machine).map (eraseOccurrenceMergeLoResult) := by
-- proof
  unfold mergeLoSucceed?
  simp only [eraseOccurrenceMergeLoMachine_state, eraseOccurrenceMergeLoMachine_na,
    eraseOccurrenceMergeLoMachine_dest, eraseOccurrenceMergeLoMachine_aPos]
  rw [eraseOccurrenceMergeLoFinalTempToData]
  cases hcopy : mergeLoMemcpyTempToData? .finalTempToData rfl machine.na
    machine.state machine.dest machine.aPos with
  | none => rfl
  | some state => simp

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoCopyB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoCopyB
  {alpha : Type u}
  {nu : Type v}
  {machine : MergeLoMachine (Occurrence alpha) nu} :
-- imply
  mergeLoCopyB? (eraseOccurrenceMergeLoMachine machine) = (mergeLoCopyB? machine).map (eraseOccurrenceMergeLoResult) := by
-- proof
  unfold mergeLoCopyB?
  by_cases hactive : machine.na = 1 ∧ 0 < machine.nb <;>
    simp only [eraseOccurrenceMergeLoMachine_state, eraseOccurrenceMergeLoMachine_na,
    eraseOccurrenceMergeLoMachine_nb, eraseOccurrenceMergeLoMachine_dest,
    eraseOccurrenceMergeLoMachine_bPos, eraseOccurrenceMergeLoMachine_aPos,
    eraseOccurrenceMergeState_data, eraseOccurrenceMergeState_tempStorage, hactive]
  · rw [eraseOccurrenceMergeDataMemmove]
    cases hmove : mergeDataMemmove? .loCopyBTail machine.state.data
      machine.dest machine.bPos machine.nb with
    | none => simp
    | some data =>
      simp only [Option.map_some, bind, Option.bind]
      rw [eraseOccurrenceMergeLoTempRead]
      cases hread : mergeLoTempRead? machine.state.a machine.aPos with
      | none => simp
      | some entry =>
        simp only [Option.map_some]
        rw [eraseOccurrenceSlice_write]
        cases hwrite : data.write?
          (machine.dest + Int.ofNat machine.nb) entry with
        | none => simp
        | some finalData =>
          simp [eraseOccurrenceMergeLoResult, eraseOccurrenceMergeState, mergeLoSuccess]
  · rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoGallopFuelFailure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoGallopFuelFailure
  {alpha : Type u}
  {nu : Type v}
  {machine : MergeLoMachine (Occurrence alpha) nu} :
-- imply
  mergeLoGallopFuelFailure (eraseOccurrenceMergeLoMachine machine) = (mergeLoGallopFuelFailure machine).map (eraseOccurrenceMergeLoResult) := by
-- proof
  rfl
set_option maxHeartbeats 2000000 in

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoGallopRound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoGallopRound
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {machine : MergeLoMachine (Occurrence alpha) nu}
  {next : MergeLoMachine (Occurrence alpha) nu → Nat → Nat → Option (MergeLoResult (Occurrence alpha) nu)}
  {next' : MergeLoMachine alpha nu → Nat → Nat → Option (MergeLoResult alpha nu)}
-- given
  (hcompare : machine.state.key_compare = occurrenceComparator lt)
  (hnext : ∀ machine aCount bCount, machine.state.key_compare = occurrenceComparator lt → next' (eraseOccurrenceMergeLoMachine machine) aCount bCount = (next machine aCount bCount).map (eraseOccurrenceMergeLoResult)) :
-- imply
  mergeLoGallopRound? (eraseOccurrenceMergeLoMachine machine) next' = (mergeLoGallopRound? machine next).map (eraseOccurrenceMergeLoResult) := by
-- proof
  unfold mergeLoGallopRound?
  simp only [eraseOccurrenceMergeLoMachine_na, eraseOccurrenceMergeLoMachine_nb,
    eraseOccurrenceMergeLoMachine_state, eraseOccurrenceMergeLoMachine_dest,
    eraseOccurrenceMergeLoMachine_aPos, eraseOccurrenceMergeLoMachine_bPos,
    eraseOccurrenceMergeLoMachine_minGallop]
  by_cases hactive : machine.na ≤ 1 ∨ machine.nb = 0 <;>
    simp only [hactive, if_pos, if_false, Option.map_none]
  rw [eraseOccurrenceMergeState_data, eraseOccurrenceSlice_read]
  cases hfirstB : machine.state.data.read? machine.bPos with
  | none => rfl
  | some firstB =>
    simp only [Option.map_some, bind, Option.bind]
    rw [eraseOccurrenceMergeState_tempStorage, eraseOccurrenceMergeLoTempRun]
    cases hactiveA : mergeLoTempRun? machine.state.a machine.aPos machine.na with
    | none => rfl
    | some activeA =>
      simp only [Option.map_some, mergeLoBindOptionAcross]
      let adjustedState : MergeState (Occurrence alpha) nu :=
        { machine.state with
          min_gallop :=
            if (1 : PySSize).slt machine.minGallop then
              machine.minGallop - 1
            else machine.minGallop }
      let adjustedMachine : MergeLoMachine (Occurrence alpha) nu :=
        { machine with
          state := adjustedState
          minGallop :=
            if (1 : PySSize).slt machine.minGallop then
              machine.minGallop - 1
            else machine.minGallop }
      have hcompare' : adjustedState.key_compare =
        occurrenceComparator lt := by
        simpa [adjustedState] using hcompare
      change
        mergeLoBindOptionAcross
          (gallopRight? (eraseOccurrenceMergeState adjustedState)
            (eraseOccurrenceSlice activeA) 0
            firstB.key.value machine.na 0) _ =
          Option.map (eraseOccurrenceMergeLoResult)
            (mergeLoBindOptionAcross
              (gallopRight? adjustedState activeA 0 firstB.key
                machine.na 0) _)
      rw [eraseOccurrenceGallopRight lt adjustedState activeA 0 firstB.key
        machine.na 0 hcompare']
      cases hgallopA : gallopRight?
        { machine.state with
          min_gallop :=
            if (1 : PySSize).slt machine.minGallop then
              machine.minGallop - 1
            else machine.minGallop }
        activeA 0 firstB.key machine.na 0 with
      | none => rfl
      | some gallopA =>
        change
          (if gallopA.fuelExhausted then
            mergeLoGallopFuelFailure
              (eraseOccurrenceMergeLoMachine adjustedMachine)
            else _) =
            Option.map (eraseOccurrenceMergeLoResult)
              (if gallopA.fuelExhausted then
                mergeLoGallopFuelFailure adjustedMachine
                else _)
        by_cases hfuel : gallopA.fuelExhausted = true
        · simp only [hfuel, if_true]
          exact eraseOccurrenceMergeLoGallopFuelFailure adjustedMachine
        · simp only [hfuel, Bool.false_eq_true, if_false]
          by_cases hindex : gallopA.index > machine.na
          · simp only [hindex, if_true, Option.map_none]
          · simp only [hindex, if_false]
            change
              Option.bind
                (mergeLoMemcpyTempToData? .gallopTempToData rfl
                  gallopA.index (eraseOccurrenceMergeState adjustedState)
                  machine.dest machine.aPos) _ =
                Option.map (eraseOccurrenceMergeLoResult)
                  (Option.bind
                    (mergeLoMemcpyTempToData? .gallopTempToData rfl
                      gallopA.index adjustedState machine.dest machine.aPos)
                    _)
            rw [eraseOccurrenceMergeLoGallopTempToData]
            cases hcopyA : mergeLoMemcpyTempToData? .gallopTempToData rfl
              gallopA.index
              { machine.state with
                min_gallop :=
                  if (1 : PySSize).slt machine.minGallop then
                    machine.minGallop - 1
                  else machine.minGallop }
              machine.dest machine.aPos with
            | none => rfl
            | some state =>
              simp only [Option.map_some, Option.bind_some]
              let afterA : MergeLoMachine (Occurrence alpha) nu :=
                { state := state
                  dest := machine.dest + Int.ofNat gallopA.index
                  aPos := machine.aPos + gallopA.index
                  bPos := machine.bPos
                  na := machine.na - gallopA.index
                  nb := machine.nb
                  minGallop :=
                    if (1 : PySSize).slt machine.minGallop then
                      machine.minGallop - 1
                    else machine.minGallop }
              change
                (if afterA.na = 0 then
                  mergeLoSucceed?
                    (eraseOccurrenceMergeLoMachine afterA)
                  else if afterA.na = 1 then
                    mergeLoCopyB? (eraseOccurrenceMergeLoMachine afterA)
                  else
                    Option.bind
                      (mergeLoCopyBIncr?
                        (eraseOccurrenceMergeLoMachine afterA)) _) =
                  Option.map (eraseOccurrenceMergeLoResult)
                    (if afterA.na = 0 then mergeLoSucceed? afterA
                      else if afterA.na = 1 then mergeLoCopyB? afterA
                      else Option.bind (mergeLoCopyBIncr? afterA) _)
              split
              · exact eraseOccurrenceMergeLoSucceed afterA
              · split
                · exact eraseOccurrenceMergeLoCopyB afterA
                · rw [eraseOccurrenceMergeLoCopyBIncr]
                  cases hcopyB : mergeLoCopyBIncr? afterA with
                  | none => rfl
                  | some afterB =>
                    simp only [Option.map_some, Option.bind_some]
                    change
                      (if afterB.nb = 0 then
                        mergeLoSucceed?
                          (eraseOccurrenceMergeLoMachine afterB)
                        else _) =
                        Option.map (eraseOccurrenceMergeLoResult)
                          (if afterB.nb = 0 then
                            mergeLoSucceed? afterB
                            else _)
                    by_cases hnb : afterB.nb = 0
                    · simp only [hnb, if_true]
                      exact eraseOccurrenceMergeLoSucceed afterB
                    · simp only [hnb, if_false]
                      change
                        Option.bind
                          (mergeLoTempRead?
                            (eraseOccurrenceTempStorage afterB.state.a)
                            afterB.aPos) _ =
                          Option.map (eraseOccurrenceMergeLoResult)
                            (Option.bind
                              (mergeLoTempRead? afterB.state.a
                                afterB.aPos) _)
                      rw [eraseOccurrenceMergeLoTempRead]
                      cases hfirstA : mergeLoTempRead? afterB.state.a
                        afterB.aPos with
                      | none => rfl
                      | some firstA =>
                        simp only [Option.map_some, Option.bind_some]
                        have hafterCompare : afterB.state.key_compare =
                          occurrenceComparator lt := by
                          calc
                            afterB.state.key_compare =
                              afterA.state.key_compare :=
                              occurrenceErasure_mergeLoCopyBIncr_key_compare_of_eq_some
                                afterA afterB hcopyB
                            _ = state.key_compare := rfl
                            _ = adjustedState.key_compare :=
                        occurrenceErasure_mergeLoMemcpyTempToData_key_compare_of_eq_some
                          .gallopTempToData rfl gallopA.index
                          adjustedState state machine.dest
                          machine.aPos hcopyA
                          _ = occurrenceComparator lt := hcompare'
                        change
                          mergeLoBindOptionAcross
                            (gallopLeft?
                              (eraseOccurrenceMergeState afterB.state)
                              (eraseOccurrenceSlice
                                afterB.state.data)
                              afterB.bPos
                              firstA.key.value
                              afterB.nb 0) _ =
                            Option.map (eraseOccurrenceMergeLoResult)
                              (mergeLoBindOptionAcross
                                (gallopLeft? afterB.state
                                  afterB.state.data afterB.bPos
                                  firstA.key afterB.nb 0) _)
                        rw [eraseOccurrenceGallopLeft lt afterB.state
                          afterB.state.data afterB.bPos firstA.key
                          afterB.nb 0 hafterCompare]
                        cases hgallopB : gallopLeft? afterB.state
                          afterB.state.data afterB.bPos firstA.key
                          afterB.nb 0 with
                        | none => rfl
                        | some gallopB =>
                          change
                            (if gallopB.fuelExhausted then
                              mergeLoGallopFuelFailure
                                (eraseOccurrenceMergeLoMachine afterB)
                              else if gallopB.index > afterB.nb then
                                none
                              else _) =
                              Option.map (eraseOccurrenceMergeLoResult)
                                (if gallopB.fuelExhausted then
                                  mergeLoGallopFuelFailure afterB
                                  else if gallopB.index > afterB.nb then
                                    none
                                  else _)
                          by_cases hfuelB :
                            gallopB.fuelExhausted = true
                          all_goals simp only [hfuelB, if_true,
                            Bool.false_eq_true, if_false]
                          all_goals first
                            | exact
                              eraseOccurrenceMergeLoGallopFuelFailure afterB
                            | skip
                          by_cases hindexB : gallopB.index > afterB.nb <;>
                            simp only [hindexB, if_true, if_false,
                              Option.map_none]
                          change
                            Option.bind
                              (mergeDataMemmove? .loGallopB
                                (eraseOccurrenceSlice
                                  afterB.state.data)
                                afterB.dest afterB.bPos
                                gallopB.index) _ =
                              Option.map (eraseOccurrenceMergeLoResult)
                                (Option.bind
                                  (mergeDataMemmove? .loGallopB
                                    afterB.state.data afterB.dest
                                    afterB.bPos gallopB.index) _)
                          rw [eraseOccurrenceMergeDataMemmove]
                          cases hmoveB : mergeDataMemmove?
                            .loGallopB afterB.state.data afterB.dest
                            afterB.bPos gallopB.index with
                          | none => rfl
                          | some data =>
                            simp only [Option.map_some,
                              Option.bind_some]
                            let movedB :
                              MergeLoMachine
                                (Occurrence alpha) nu :=
                              { afterB with
                                state :=
                                  { afterB.state with data := data }
                                dest := afterB.dest +
                                  Int.ofNat gallopB.index
                                bPos := afterB.bPos +
                                  Int.ofNat gallopB.index
                                nb := afterB.nb - gallopB.index }
                            change
                              (if movedB.nb = 0 then
                                mergeLoSucceed?
                                  (eraseOccurrenceMergeLoMachine
                                    movedB)
                                else
                                  Option.bind
                                    (mergeLoCopyAIncr?
                                      (eraseOccurrenceMergeLoMachine
                                        movedB)) _) =
                                Option.map
                                  (eraseOccurrenceMergeLoResult)
                                  (if movedB.nb = 0 then
                                    mergeLoSucceed? movedB
                                    else
                                      Option.bind
                                        (mergeLoCopyAIncr? movedB)
                                        _)
                            split
                            · exact
                              eraseOccurrenceMergeLoSucceed movedB
                            · rw [eraseOccurrenceMergeLoCopyAIncr]
                              cases hcopyAOne :
                                mergeLoCopyAIncr? movedB with
                              | none => rfl
                              | some afterA =>
                                simp only [Option.map_some,
                                  Option.bind_some]
                                change
                                  (if afterA.na = 1 then
                                    mergeLoCopyB?
                                      (eraseOccurrenceMergeLoMachine afterA)
                                    else next'
                                      (eraseOccurrenceMergeLoMachine afterA)
                                      gallopA.index
                                      gallopB.index) =
                                    Option.map
                                      (eraseOccurrenceMergeLoResult)
                                      (if afterA.na = 1 then
                                        mergeLoCopyB? afterA
                                        else next afterA
                                          gallopA.index
                                          gallopB.index)
                                split
                                · exact
                                  eraseOccurrenceMergeLoCopyB
                                    afterA
                                · apply hnext afterA
                                  gallopA.index gallopB.index
                                  calc
                                    afterA.state.key_compare =
                                      movedB.state.key_compare :=
                          occurrenceErasure_mergeLoCopyAIncr_key_compare_of_eq_some
                            movedB afterA hcopyAOne
                            _ = afterB.state.key_compare :=
                              rfl
                            _ = occurrenceComparator lt :=
                              hafterCompare
set_option maxHeartbeats 2000000 in

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLoLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLoLoop
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {fuel : Nat}
  {machine : MergeLoMachine (Occurrence alpha) nu}
  {phase : MergeLoPhase}
-- given
  (hcompare : machine.state.key_compare = occurrenceComparator lt) :
-- imply
  mergeLoLoop? fuel (eraseOccurrenceMergeLoMachine machine) phase = (mergeLoLoop? fuel machine phase).map (eraseOccurrenceMergeLoResult) := by
-- proof
  induction fuel generalizing machine phase with
  | zero => simp [mergeLoLoop?, eraseOccurrenceMergeLoResult]
  | succ fuel ih =>
    cases phase with
    | ordinary aCount bCount =>
      simp only [mergeLoLoop?]
      simp only [eraseOccurrenceMergeLoMachine_na, eraseOccurrenceMergeLoMachine_nb,
        eraseOccurrenceMergeLoMachine_state, eraseOccurrenceMergeLoMachine_aPos,
        eraseOccurrenceMergeLoMachine_bPos]
      by_cases hactive : machine.na ≤ 1 ∨ machine.nb = 0 <;>
        simp only [hactive, if_pos, if_false, Option.map_none]
      rw [eraseOccurrenceMergeState_tempStorage, eraseOccurrenceMergeLoTempRead]
      cases hfirstA : mergeLoTempRead? machine.state.a machine.aPos with
      | none => rfl
      | some firstA =>
        simp only [Option.map_some, bind, Option.bind]
        rw [eraseOccurrenceMergeState_data, eraseOccurrenceSlice_read]
        cases hfirstB : machine.state.data.read? machine.bPos with
        | none => rfl
        | some firstB =>
          simp only [Option.map_some]
          simp only [eraseOccurrenceMergeState_key_compare, hcompare,
            eraseOccurrenceComparator_occurrenceComparator,
            eraseOccurrenceEntry_key,
            iflt_eraseOccurrence]
          split
          · rw [eraseOccurrenceMergeLoCopyBIncr]
            cases hcopy : mergeLoCopyBIncr? machine with
            | none => rfl
            | some next =>
              simp only [Option.map_some]
              have hnextCompare : next.state.key_compare =
                occurrenceComparator lt :=
                (occurrenceErasure_mergeLoCopyBIncr_key_compare_of_eq_some
                  machine next hcopy).trans hcompare
              let raised : MergeLoMachine (Occurrence alpha) nu :=
                { next with minGallop := next.minGallop + 1 }
              simp only [eraseOccurrenceMergeLoMachine_nb,
                eraseOccurrenceMergeLoMachine_na,
                eraseOccurrenceMergeLoMachine_minGallop]
              change
                (if next.nb = 0 then
                  mergeLoSucceed?
                    (eraseOccurrenceMergeLoMachine next)
                  else if mergeLoCountAtLeastWord (bCount + 1)
                    next.minGallop then
                    mergeLoLoop? fuel
                      (eraseOccurrenceMergeLoMachine raised) .galloping
                  else
                    mergeLoLoop? fuel
                      (eraseOccurrenceMergeLoMachine next)
                      (.ordinary 0 (bCount + 1))) =
                  Option.map (eraseOccurrenceMergeLoResult)
                    (if next.nb = 0 then mergeLoSucceed? next
                      else if mergeLoCountAtLeastWord (bCount + 1)
                        next.minGallop then
                        mergeLoLoop? fuel raised .galloping
                      else
                        mergeLoLoop? fuel next
                          (.ordinary 0 (bCount + 1)))
              split
              · exact eraseOccurrenceMergeLoSucceed next
              · split
                · apply ih raised .galloping
                  simpa [raised] using hnextCompare
                · exact ih next (.ordinary 0 (bCount + 1))
                  hnextCompare
          · rw [eraseOccurrenceMergeLoCopyAIncr]
            cases hcopy : mergeLoCopyAIncr? machine with
            | none => rfl
            | some next =>
              simp only [Option.map_some]
              have hnextCompare : next.state.key_compare =
                occurrenceComparator lt :=
                (occurrenceErasure_mergeLoCopyAIncr_key_compare_of_eq_some
                  machine next hcopy).trans hcompare
              let raised : MergeLoMachine (Occurrence alpha) nu :=
                { next with minGallop := next.minGallop + 1 }
              simp only [eraseOccurrenceMergeLoMachine_nb,
                eraseOccurrenceMergeLoMachine_na,
                eraseOccurrenceMergeLoMachine_minGallop]
              change
                (if next.na = 1 then
                  mergeLoCopyB?
                    (eraseOccurrenceMergeLoMachine next)
                  else if mergeLoCountAtLeastWord (aCount + 1)
                    next.minGallop then
                    mergeLoLoop? fuel
                      (eraseOccurrenceMergeLoMachine raised) .galloping
                  else
                    mergeLoLoop? fuel
                      (eraseOccurrenceMergeLoMachine next)
                      (.ordinary (aCount + 1) 0)) =
                  Option.map (eraseOccurrenceMergeLoResult)
                    (if next.na = 1 then mergeLoCopyB? next
                      else if mergeLoCountAtLeastWord (aCount + 1)
                        next.minGallop then
                        mergeLoLoop? fuel raised .galloping
                      else
                        mergeLoLoop? fuel next
                          (.ordinary (aCount + 1) 0))
              split
              · exact eraseOccurrenceMergeLoCopyB next
              · split
                · apply ih raised .galloping
                  simpa [raised] using hnextCompare
                · exact ih next (.ordinary (aCount + 1) 0)
                  hnextCompare
    | galloping =>
      apply eraseOccurrenceMergeLoGallopRound lt machine _ _ hcompare
      intro next aCount bCount hnextCompare
      split
      · exact ih next .galloping hnextCompare
      · let minGallop := next.minGallop + 1
        let adjustedState := { next.state with min_gallop := minGallop }
        let adjusted : MergeLoMachine (Occurrence alpha) nu :=
          { next with state := adjustedState, minGallop := minGallop }
        change
          mergeLoLoop? fuel (eraseOccurrenceMergeLoMachine adjusted)
            (.ordinary 0 0) =
            Option.map (eraseOccurrenceMergeLoResult)
              (mergeLoLoop? fuel adjusted (.ordinary 0 0))
        apply ih adjusted (.ordinary 0 0)
        simpa [adjusted, adjustedState] using hnextCompare

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeLo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeLo
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {state : MergeState (Occurrence alpha) nu}
  {ssa ssb : Int}
  {na nb : Nat}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  mergeLo? (eraseOccurrenceMergeState state) ssa ssb na nb = (mergeLo? state ssa ssb na nb).map (eraseOccurrenceMergeLoResult) := by
-- proof
  unfold mergeLo?
  split <;> try rfl
  rw [eraseOccurrenceMergeGetmem]
  cases hallocated : mergeGetmem state (BitVec.ofNat 64 na) with
  | mk allocatedState outcome =>
    cases outcome with
    | guardRejected => simp
    | reused =>
      simp only [eraseOccurrenceMergeGetmemResult]
      simp only [reduceCtorEq, if_false]
      rw [eraseOccurrenceMergeLoInitialDataToTemp]
      cases hcopy : mergeLoMemcpyDataToTemp? .initialDataToTemp rfl na
        allocatedState 0 ssa with
      | none => rfl
      | some copiedState =>
        simp only [Option.map_some, bind, Option.bind]
        let initial : MergeLoMachine (Occurrence alpha) nu :=
          { state := copiedState, dest := ssa, aPos := 0, bPos := ssb,
            na := na, nb := nb, minGallop := copiedState.min_gallop }
        change
          Option.bind (mergeLoCopyBIncr?
            (eraseOccurrenceMergeLoMachine initial)) _ =
            Option.map (eraseOccurrenceMergeLoResult)
              (Option.bind (mergeLoCopyBIncr? initial) _)
        rw [eraseOccurrenceMergeLoCopyBIncr]
        cases hfirst : mergeLoCopyBIncr? initial with
        | none => rfl
        | some machine =>
          simp only [Option.map_some, Option.bind_some]
          have hallocatedCompare : allocatedState.key_compare =
            state.key_compare := by
            have hframe := mergeGetmem_key_compare state
              (BitVec.ofNat 64 na)
            simpa [hallocated] using hframe
          have hmachineCompare : machine.state.key_compare =
            occurrenceComparator lt := by
            calc
              machine.state.key_compare = initial.state.key_compare :=
                occurrenceErasure_mergeLoCopyBIncr_key_compare_of_eq_some initial machine
                  hfirst
              _ = copiedState.key_compare := rfl
              _ = allocatedState.key_compare :=
                occurrenceErasure_mergeLoMemcpyDataToTemp_key_compare_of_eq_some
                  .initialDataToTemp rfl na allocatedState copiedState 0
                  ssa hcopy
              _ = state.key_compare := hallocatedCompare
              _ = occurrenceComparator lt := hcompare
          change
            (if machine.nb = 0 then
              mergeLoSucceed? (eraseOccurrenceMergeLoMachine machine)
              else if machine.na = 1 then
                mergeLoCopyB? (eraseOccurrenceMergeLoMachine machine)
              else
                mergeLoLoop? (na + nb + 1)
                  (eraseOccurrenceMergeLoMachine machine)
                  (.ordinary 0 0)) =
              Option.map (eraseOccurrenceMergeLoResult)
                (if machine.nb = 0 then mergeLoSucceed? machine
                  else if machine.na = 1 then mergeLoCopyB? machine
                  else mergeLoLoop? (na + nb + 1) machine
                    (.ordinary 0 0))
          split
          · exact eraseOccurrenceMergeLoSucceed machine
          · split
            · exact eraseOccurrenceMergeLoCopyB machine
            · exact eraseOccurrenceMergeLoLoop lt (na + nb + 1) machine
              (.ordinary 0 0) hmachineCompare
    | grown =>
      simp only [eraseOccurrenceMergeGetmemResult]
      simp only [reduceCtorEq, if_false]
      rw [eraseOccurrenceMergeLoInitialDataToTemp]
      cases hcopy : mergeLoMemcpyDataToTemp? .initialDataToTemp rfl na
        allocatedState 0 ssa with
      | none => rfl
      | some copiedState =>
        simp only [Option.map_some, bind, Option.bind]
        let initial : MergeLoMachine (Occurrence alpha) nu :=
          { state := copiedState, dest := ssa, aPos := 0, bPos := ssb,
            na := na, nb := nb, minGallop := copiedState.min_gallop }
        change
          Option.bind (mergeLoCopyBIncr?
            (eraseOccurrenceMergeLoMachine initial)) _ =
            Option.map (eraseOccurrenceMergeLoResult)
              (Option.bind (mergeLoCopyBIncr? initial) _)
        rw [eraseOccurrenceMergeLoCopyBIncr]
        cases hfirst : mergeLoCopyBIncr? initial with
        | none => rfl
        | some machine =>
          simp only [Option.map_some, Option.bind_some]
          have hallocatedCompare : allocatedState.key_compare =
            state.key_compare := by
            have hframe := mergeGetmem_key_compare state
              (BitVec.ofNat 64 na)
            simpa [hallocated] using hframe
          have hmachineCompare : machine.state.key_compare =
            occurrenceComparator lt := by
            calc
              machine.state.key_compare = initial.state.key_compare :=
                occurrenceErasure_mergeLoCopyBIncr_key_compare_of_eq_some initial machine
                  hfirst
              _ = copiedState.key_compare := rfl
              _ = allocatedState.key_compare :=
                occurrenceErasure_mergeLoMemcpyDataToTemp_key_compare_of_eq_some
                  .initialDataToTemp rfl na allocatedState copiedState 0
                  ssa hcopy
              _ = state.key_compare := hallocatedCompare
              _ = occurrenceComparator lt := hcompare
          change
            (if machine.nb = 0 then
              mergeLoSucceed? (eraseOccurrenceMergeLoMachine machine)
              else if machine.na = 1 then
                mergeLoCopyB? (eraseOccurrenceMergeLoMachine machine)
              else
                mergeLoLoop? (na + nb + 1)
                  (eraseOccurrenceMergeLoMachine machine)
                  (.ordinary 0 0)) =
              Option.map (eraseOccurrenceMergeLoResult)
                (if machine.nb = 0 then mergeLoSucceed? machine
                  else if machine.na = 1 then mergeLoCopyB? machine
                  else mergeLoLoop? (na + nb + 1) machine
                    (.ordinary 0 0))
          split
          · exact eraseOccurrenceMergeLoSucceed machine
          · split
            · exact eraseOccurrenceMergeLoCopyB machine
            · exact eraseOccurrenceMergeLoLoop lt (na + nb + 1) machine
              (.ordinary 0 0) hmachineCompare

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeHiTempRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeHiTempRead
  {alpha : Type u}
  {nu : Type v}
  {storage : TempStorage (Occurrence alpha) nu}
  {index : Int} :
-- imply
  mergeHiTempRead? (eraseOccurrenceTempStorage storage) index = (mergeHiTempRead? storage index).map (eraseOccurrenceEntry) := by
-- proof
  unfold mergeHiTempRead?
  by_cases hnonnegative : 0 ≤ index
  · simp only [hnonnegative, if_true]
    cases hcell : storage.cells[index.toNat]? with
    | none => simp [eraseOccurrenceTempStorage, hcell]
    | some cell => cases cell <;> simp [eraseOccurrenceTempStorage, hcell]
  · simp [hnonnegative]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeHiTempWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeHiTempWrite
  {alpha : Type u}
  {nu : Type v}
  {storage : TempStorage (Occurrence alpha) nu}
  {index : Int}
  {entry : SortSliceEntry (Occurrence alpha) nu} :
-- imply
  mergeHiTempWrite? (eraseOccurrenceTempStorage storage) index (eraseOccurrenceEntry entry) = (mergeHiTempWrite? storage index entry).map (eraseOccurrenceTempStorage) := by
-- proof
  unfold mergeHiTempWrite?
  split <;> try rfl
  simp only [eraseOccurrenceTempStorage_cells_size]
  split
  · simp [eraseOccurrenceTempStorage, Array.map_set]
  · rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeHiCopyDataToTemp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeHiCopyDataToTemp
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  mergeHiCopyDataToTemp? (eraseOccurrenceMergeState state) dst src = (mergeHiCopyDataToTemp? state dst src).map (eraseOccurrenceMergeState) := by
-- proof
  unfold mergeHiCopyDataToTemp?
  simp only [eraseOccurrenceMergeState_data, eraseOccurrenceMergeState_tempStorage,
    eraseOccurrenceMergeState_minGallop, eraseOccurrenceMergeState_listlen,
    eraseOccurrenceMergeState_basekeys, eraseOccurrenceMergeState_alloced,
    eraseOccurrenceMergeState_pending, eraseOccurrenceMergeState_key_compare,
    eraseOccurrenceMergeState_mrCurrent, eraseOccurrenceMergeState_mrE,
    eraseOccurrenceMergeState_mrMask]
  rw [eraseOccurrenceSlice_read]
  cases hread : state.data.read? src with
  | none => rfl
  | some entry =>
    simp only [Option.map_some, bind, Option.bind]
    rw [eraseOccurrenceMergeHiTempWrite]
    cases hwrite : mergeHiTempWrite? state.a dst entry with
    | none => rfl
    | some storage => simp [eraseOccurrenceMergeState]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeHiCopyTempToData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeHiCopyTempToData
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  mergeHiCopyTempToData? (eraseOccurrenceMergeState state) dst src = (mergeHiCopyTempToData? state dst src).map (eraseOccurrenceMergeState) := by
-- proof
  unfold mergeHiCopyTempToData?
  simp only [eraseOccurrenceMergeState_data, eraseOccurrenceMergeState_tempStorage,
    eraseOccurrenceMergeState_minGallop, eraseOccurrenceMergeState_listlen,
    eraseOccurrenceMergeState_basekeys, eraseOccurrenceMergeState_alloced,
    eraseOccurrenceMergeState_pending, eraseOccurrenceMergeState_key_compare,
    eraseOccurrenceMergeState_mrCurrent, eraseOccurrenceMergeState_mrE,
    eraseOccurrenceMergeState_mrMask]
  rw [eraseOccurrenceMergeHiTempRead]
  cases hread : mergeHiTempRead? state.a src with
  | none => rfl
  | some entry =>
    simp only [Option.map_some, bind, Option.bind]
    rw [eraseOccurrenceSlice_write]
    cases hwrite : state.data.write? dst entry with
    | none => rfl
    | some data => simp [eraseOccurrenceMergeState]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeHiMemcpyDataToTemp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeHiMemcpyDataToTemp
  {alpha : Type u}
  {nu : Type v}
  {site : MergeHiMemcpyCallsite}
  {count : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {dst src : Int}
-- given
  (hDirection : site.backings = { destination := .temporary, source := .main }) :
-- imply
  mergeHiMemcpyDataToTemp? site hDirection count (eraseOccurrenceMergeState state) dst src = (mergeHiMemcpyDataToTemp? site hDirection count state dst src).map (eraseOccurrenceMergeState) := by
-- proof
  induction count generalizing state dst src with
  | zero => rfl
  | succ count ih =>
    simp only [mergeHiMemcpyDataToTemp?]
    rw [eraseOccurrenceMergeHiCopyDataToTemp]
    cases hcopy : mergeHiCopyDataToTemp? state dst src with
    | none => rfl
    | some state =>
      simp only [Option.map_some]
      exact ih (state := state) (dst := dst + 1) (src := src + 1)

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeHiMemcpyTempToData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeHiMemcpyTempToData
  {alpha : Type u}
  {nu : Type v}
  {site : MergeHiMemcpyCallsite}
  {count : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {dst src : Int}
-- given
  (hDirection : site.backings = { destination := .main, source := .temporary }) :
-- imply
  mergeHiMemcpyTempToData? site hDirection count (eraseOccurrenceMergeState state) dst src = (mergeHiMemcpyTempToData? site hDirection count state dst src).map (eraseOccurrenceMergeState) := by
-- proof
  induction count generalizing state dst src with
  | zero => rfl
  | succ count ih =>
    simp only [mergeHiMemcpyTempToData?]
    rw [eraseOccurrenceMergeHiCopyTempToData]
    cases hcopy : mergeHiCopyTempToData? state dst src with
    | none => rfl
    | some state =>
      simp only [Option.map_some]
      exact ih (state := state) (dst := dst + 1) (src := src + 1)

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeHiInitialDataToTemp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeHiInitialDataToTemp
  {alpha : Type u}
  {nu : Type v}
  {count : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  mergeHiMemcpyDataToTemp? .initialDataToTemp rfl count (eraseOccurrenceMergeState state) dst src = (mergeHiMemcpyDataToTemp? .initialDataToTemp rfl count state dst src).map (eraseOccurrenceMergeState) := by
-- proof
  exact eraseOccurrenceMergeHiMemcpyDataToTemp .initialDataToTemp rfl count state
    dst src

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeHiGallopTempToData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeHiGallopTempToData
  {alpha : Type u}
  {nu : Type v}
  {count : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  mergeHiMemcpyTempToData? .gallopTempToData rfl count (eraseOccurrenceMergeState state) dst src = (mergeHiMemcpyTempToData? .gallopTempToData rfl count state dst src).map (eraseOccurrenceMergeState) := by
-- proof
  exact eraseOccurrenceMergeHiMemcpyTempToData .gallopTempToData rfl count state
    dst src

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeHiFinalTempToData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeHiFinalTempToData
  {alpha : Type u}
  {nu : Type v}
  {count : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  mergeHiMemcpyTempToData? .finalTempToData rfl count (eraseOccurrenceMergeState state) dst src = (mergeHiMemcpyTempToData? .finalTempToData rfl count state dst src).map (eraseOccurrenceMergeState) := by
-- proof
  exact eraseOccurrenceMergeHiMemcpyTempToData .finalTempToData rfl count state
    dst src

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeHiInitializedTempPrefixLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeHiInitializedTempPrefixLoop
  {alpha : Type u}
  {nu : Type v}
  {count : Nat}
  {storage : TempStorage (Occurrence alpha) nu}
  {source : Nat}
  {entries : Array (SortSliceEntry (Occurrence alpha) nu)} :
-- imply
  mergeHiInitializedTempPrefixLoop? count (eraseOccurrenceTempStorage storage) source (entries.map (eraseOccurrenceEntry)) = (mergeHiInitializedTempPrefixLoop? count storage source entries).map (Array.map (eraseOccurrenceEntry)) := by
-- proof
  induction count generalizing source entries with
  | zero => rfl
  | succ count ih =>
    simp only [mergeHiInitializedTempPrefixLoop?]
    rw [eraseOccurrenceMergeHiTempRead]
    cases hread : mergeHiTempRead? storage (Int.ofNat source) with
    | none => rfl
    | some entry =>
      simp only [Option.map_some]
      simpa [Array.map_push] using
        ih (source := source + 1) (entries := entries.push entry)

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceInitializedTempPrefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceInitializedTempPrefix
  {alpha : Type u}
  {nu : Type v}
  {storage : TempStorage (Occurrence alpha) nu}
  {count : Nat} :
-- imply
  initializedTempPrefix? (eraseOccurrenceTempStorage storage) count = (initializedTempPrefix? storage count).map (eraseOccurrenceSlice) := by
-- proof
  unfold initializedTempPrefix?
  have hloop :
    mergeHiInitializedTempPrefixLoop? count
      (eraseOccurrenceTempStorage storage) 0 #[] =
      (mergeHiInitializedTempPrefixLoop? count storage 0 #[]).map
        (Array.map (eraseOccurrenceEntry)) := by
    simpa using
      eraseOccurrenceMergeHiInitializedTempPrefixLoop count storage 0 #[]
  rw [hloop]
  cases hentries : mergeHiInitializedTempPrefixLoop? count storage 0 #[] with
  | none => rfl
  | some entries => simp [eraseOccurrenceSlice]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeHiCursor_minGallop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeHiCursor_minGallop
  {alpha : Type u}
  {nu : Type v}
  {cursor : MergeHiCursor (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeHiCursor cursor).minGallop = cursor.minGallop :=
-- proof
  rfl
@[simp] theorem eraseOccurrenceMergeHiCursor_phase (cursor : MergeHiCursor (Occurrence alpha) nu) :
  (eraseOccurrenceMergeHiCursor cursor).phase = cursor.phase := rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeHiCopyDataDecr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeHiCopyDataDecr
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  mergeHiCopyDataDecr? (eraseOccurrenceMergeState state) dst src = (mergeHiCopyDataDecr? state dst src).map (eraseOccurrenceMergeHiDataCursorResult) := by
-- proof
  unfold mergeHiCopyDataDecr?
  simp only [eraseOccurrenceMergeState_data, eraseOccurrenceMergeState_tempStorage,
    eraseOccurrenceMergeState_minGallop, eraseOccurrenceMergeState_listlen,
    eraseOccurrenceMergeState_basekeys, eraseOccurrenceMergeState_alloced,
    eraseOccurrenceMergeState_pending, eraseOccurrenceMergeState_key_compare,
    eraseOccurrenceMergeState_mrCurrent, eraseOccurrenceMergeState_mrE,
    eraseOccurrenceMergeState_mrMask]
  rw [eraseOccurrenceSlice_copyDecr]
  cases hcopy : state.data.copyDecr? dst src with
  | none => rfl
  | some copied => simp [eraseOccurrenceMergeHiDataCursorResult, eraseOccurrenceMergeState,
    eraseOccurrenceCursorResult]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeHiCopyTempDecr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeHiCopyTempDecr
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  mergeHiCopyTempDecr? (eraseOccurrenceMergeState state) dst src = (mergeHiCopyTempDecr? state dst src).map (eraseOccurrenceMergeHiDataCursorResult) := by
-- proof
  unfold mergeHiCopyTempDecr?
  rw [eraseOccurrenceMergeHiCopyTempToData]
  cases hcopy : mergeHiCopyTempToData? state dst src with
  | none => rfl
  | some state => simp [eraseOccurrenceMergeHiDataCursorResult]

end CPythonListsort

namespace CPythonListsort

/--
[occurrenceErasure_mergeHiMemcpyDataToTemp_key_compare_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma occurrenceErasure_mergeHiMemcpyDataToTemp_key_compare_of_eq_some
  {alpha : Type u}
  {nu : Type v}
  {site : MergeHiMemcpyCallsite}
  {count : Nat}
  {state result : MergeState κ ν}
  {dst src : Int}
-- given
  (hDirection : site.backings = { destination := .temporary, source := .main })
  (hcopy : mergeHiMemcpyDataToTemp? site hDirection count state dst src = some result) :
-- imply
  result.key_compare = state.key_compare := by
-- proof
  induction count generalizing state dst src with
  | zero =>
    simp only [mergeHiMemcpyDataToTemp?] at hcopy
    injection hcopy with hcopy
    subst result
    rfl
  | succ count ih =>
    simp only [mergeHiMemcpyDataToTemp?] at hcopy
    cases hhead : mergeHiCopyDataToTemp? state dst src with
    | none => simp [hhead] at hcopy
    | some afterHead =>
      have htail : mergeHiMemcpyDataToTemp? site hDirection count
        afterHead (dst + 1) (src + 1) = some result := by
        simpa [hhead] using hcopy
      calc
        result.key_compare = afterHead.key_compare :=
          ih afterHead (dst + 1) (src + 1) htail
        _ = state.key_compare := by
          unfold mergeHiCopyDataToTemp? at hhead
          rcases Option.bind_eq_some_iff.mp hhead with
            ⟨entry, _hread, hhead⟩
          rcases Option.bind_eq_some_iff.mp hhead with
            ⟨storage, _hwrite, hstate⟩
          injection hstate with hstate
          subst afterHead
          rfl

end CPythonListsort

namespace CPythonListsort

/--
[occurrenceErasure_mergeHiMemcpyTempToData_key_compare_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma occurrenceErasure_mergeHiMemcpyTempToData_key_compare_of_eq_some
  {alpha : Type u}
  {nu : Type v}
  {site : MergeHiMemcpyCallsite}
  {count : Nat}
  {state result : MergeState κ ν}
  {dst src : Int}
-- given
  (hDirection : site.backings = { destination := .main, source := .temporary })
  (hcopy : mergeHiMemcpyTempToData? site hDirection count state dst src = some result) :
-- imply
  result.key_compare = state.key_compare := by
-- proof
  induction count generalizing state dst src with
  | zero =>
    simp only [mergeHiMemcpyTempToData?] at hcopy
    injection hcopy with hcopy
    subst result
    rfl
  | succ count ih =>
    simp only [mergeHiMemcpyTempToData?] at hcopy
    cases hhead : mergeHiCopyTempToData? state dst src with
    | none => simp [hhead] at hcopy
    | some afterHead =>
      have htail : mergeHiMemcpyTempToData? site hDirection count
        afterHead (dst + 1) (src + 1) = some result := by
        simpa [hhead] using hcopy
      calc
        result.key_compare = afterHead.key_compare :=
          ih afterHead (dst + 1) (src + 1) htail
        _ = state.key_compare := by
          unfold mergeHiCopyTempToData? at hhead
          rcases Option.bind_eq_some_iff.mp hhead with
            ⟨entry, _hread, hhead⟩
          rcases Option.bind_eq_some_iff.mp hhead with
            ⟨data, _hwrite, hstate⟩
          injection hstate with hstate
          subst afterHead
          rfl

end CPythonListsort

namespace CPythonListsort

/--
[occurrenceErasure_mergeHiCopyDataDecr_key_compare_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma occurrenceErasure_mergeHiCopyDataDecr_key_compare_of_eq_some
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState κ ν}
  {dst src : Int}
  {result : MergeHiDataCursorResult κ ν}
-- given
  (hcopy : mergeHiCopyDataDecr? state dst src = some result) :
-- imply
  result.state.key_compare = state.key_compare := by
-- proof
  unfold mergeHiCopyDataDecr? at hcopy
  obtain ⟨copied, _hcopied, hresult⟩ := Option.bind_eq_some_iff.mp hcopy
  injection hresult with hresult
  subst result
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[occurrenceErasure_mergeHiCopyTempDecr_key_compare_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma occurrenceErasure_mergeHiCopyTempDecr_key_compare_of_eq_some
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState κ ν}
  {dst src : Int}
  {result : MergeHiDataCursorResult κ ν}
-- given
  (hcopy : mergeHiCopyTempDecr? state dst src = some result) :
-- imply
  result.state.key_compare = state.key_compare := by
-- proof
  unfold mergeHiCopyTempDecr? at hcopy
  obtain ⟨afterCopy, hafter, hresult⟩ := Option.bind_eq_some_iff.mp hcopy
  injection hresult with hresult
  subst result
  unfold mergeHiCopyTempToData? at hafter
  obtain ⟨entry, _hread, hafter⟩ := Option.bind_eq_some_iff.mp hafter
  obtain ⟨data, _hwrite, hstate⟩ := Option.bind_eq_some_iff.mp hafter
  injection hstate with hstate
  subst afterCopy
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeHiFuelExhausted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeHiFuelExhausted
  {alpha : Type u}
  {nu : Type v}
  {cursor : MergeHiCursor (Occurrence alpha) nu} :
-- imply
  mergeHiFuelExhausted (eraseOccurrenceMergeHiCursor cursor) = eraseOccurrenceMergeHiResult (mergeHiFuelExhausted cursor) :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeHiSucceed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeHiSucceed
  {alpha : Type u}
  {nu : Type v}
  {cursor : MergeHiCursor (Occurrence alpha) nu} :
-- imply
  mergeHiSucceed? (eraseOccurrenceMergeHiCursor cursor) = (mergeHiSucceed? cursor).map (eraseOccurrenceMergeHiResult) := by
-- proof
  unfold mergeHiSucceed?
  simp only [eraseOccurrenceMergeHiCursor_nb, eraseOccurrenceMergeHiCursor_state,
    eraseOccurrenceMergeHiCursor_dest]
  by_cases hnb : cursor.nb = 0
  · simp [hnb, eraseOccurrenceMergeHiResult]
  · simp only [hnb, if_false]
    change
      Option.bind
        (mergeHiMemcpyTempToData? .finalTempToData rfl cursor.nb
          (eraseOccurrenceMergeState cursor.state)
          (cursor.dest - Int.ofNat (cursor.nb - 1)) 0) _ =
        Option.map (eraseOccurrenceMergeHiResult)
          (Option.bind
            (mergeHiMemcpyTempToData? .finalTempToData rfl cursor.nb
              cursor.state (cursor.dest - Int.ofNat (cursor.nb - 1)) 0) _)
    rw [eraseOccurrenceMergeHiFinalTempToData]
    cases hcopy : mergeHiMemcpyTempToData? .finalTempToData rfl cursor.nb
      cursor.state (cursor.dest - Int.ofNat (cursor.nb - 1)) 0 with
    | none => rfl
    | some state => simp [eraseOccurrenceMergeHiResult]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeHiCopyA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeHiCopyA
  {alpha : Type u}
  {nu : Type v}
  {cursor : MergeHiCursor (Occurrence alpha) nu} :
-- imply
  mergeHiCopyA? (eraseOccurrenceMergeHiCursor cursor) = (mergeHiCopyA? cursor).map (eraseOccurrenceMergeHiResult) := by
-- proof
  unfold mergeHiCopyA?
  simp only [eraseOccurrenceMergeHiCursor_state, eraseOccurrenceMergeHiCursor_dest,
    eraseOccurrenceMergeHiCursor_ssa, eraseOccurrenceMergeHiCursor_ssb,
    eraseOccurrenceMergeHiCursor_na, eraseOccurrenceMergeState_data,
    eraseOccurrenceMergeState_tempStorage, eraseOccurrenceMergeState_minGallop,
    eraseOccurrenceMergeState_listlen, eraseOccurrenceMergeState_basekeys,
    eraseOccurrenceMergeState_alloced, eraseOccurrenceMergeState_pending,
    eraseOccurrenceMergeState_key_compare, eraseOccurrenceMergeState_mrCurrent,
    eraseOccurrenceMergeState_mrE, eraseOccurrenceMergeState_mrMask]
  change
    (if cursor.nb = 1 ∧ 0 < cursor.na then _ else none) =
      Option.map (eraseOccurrenceMergeHiResult)
        (if cursor.nb = 1 ∧ 0 < cursor.na then _ else none)
  by_cases hactive : cursor.nb = 1 ∧ 0 < cursor.na <;>
    simp only [hactive, if_false, Option.map_none]
  rw [eraseOccurrenceMergeDataMemmove]
  cases hmove : mergeDataMemmove? .hiCopyATail cursor.state.data
    (cursor.dest + (1 - Int.ofNat cursor.na))
    (cursor.ssa + (1 - Int.ofNat cursor.na)) cursor.na with
  | none => rfl
  | some data =>
    simp only [Option.map_some, bind, Option.bind]
    let movedState : MergeState (Occurrence alpha) nu :=
      { cursor.state with data := data }
    change
      Option.bind
        (mergeHiCopyTempToData? (eraseOccurrenceMergeState movedState)
          (cursor.dest - Int.ofNat cursor.na) cursor.ssb) _ =
        Option.map (eraseOccurrenceMergeHiResult)
          (Option.bind
            (mergeHiCopyTempToData? movedState
              (cursor.dest - Int.ofNat cursor.na) cursor.ssb) _)
    rw [eraseOccurrenceMergeHiCopyTempToData]
    cases hcopy : mergeHiCopyTempToData? movedState
      (cursor.dest - Int.ofNat cursor.na) cursor.ssb with
    | none => rfl
    | some state => simp [eraseOccurrenceMergeHiResult]
set_option maxHeartbeats 2000000 in

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeHiGallopB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeHiGallopB
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {afterB : MergeHiCursor (Occurrence alpha) nu}
  {aCount : Nat}
  {next : MergeHiCursor (Occurrence alpha) nu → Option (MergeHiResult (Occurrence alpha) nu)}
  {next' : MergeHiCursor alpha nu → Option (MergeHiResult alpha nu)}
-- given
  (hcompare : afterB.state.key_compare = occurrenceComparator lt)
  (hnext : ∀ cursor, cursor.state.key_compare = occurrenceComparator lt → next' (eraseOccurrenceMergeHiCursor cursor) = (next cursor).map (eraseOccurrenceMergeHiResult)) :
-- imply
  mergeHiGallopB? (eraseOccurrenceMergeHiCursor afterB) aCount next' = (mergeHiGallopB? afterB aCount next).map (eraseOccurrenceMergeHiResult) := by
-- proof
  unfold mergeHiGallopB?
  simp only [eraseOccurrenceMergeHiCursor_state, eraseOccurrenceMergeHiCursor_ssa,
    eraseOccurrenceMergeHiCursor_nb, eraseOccurrenceMergeHiCursor_dest,
    eraseOccurrenceMergeHiCursor_ssb, eraseOccurrenceMergeHiCursor_na,
    eraseOccurrenceMergeHiCursor_minGallop]
  rw [eraseOccurrenceMergeState_data, eraseOccurrenceSlice_read]
  cases hleft : afterB.state.data.read? afterB.ssa with
  | none => rfl
  | some left =>
    simp only [Option.map_some, bind, Option.bind]
    rw [eraseOccurrenceMergeState_tempStorage, eraseOccurrenceInitializedTempPrefix]
    cases htemp : initializedTempPrefix? afterB.state.a afterB.nb with
    | none => rfl
    | some temp =>
      simp only [Option.map_some, mergeHiBindOptionAcross]
      change
        mergeHiBindOptionAcross
          (gallopLeft? (eraseOccurrenceMergeState afterB.state)
            (eraseOccurrenceSlice temp) 0
            left.key.value afterB.nb
            (afterB.nb - 1)) _ =
          Option.map (eraseOccurrenceMergeHiResult)
            (mergeHiBindOptionAcross
              (gallopLeft? afterB.state temp 0 left.key afterB.nb
                (afterB.nb - 1)) _)
      rw [eraseOccurrenceGallopLeft lt afterB.state temp 0 left.key afterB.nb
        (afterB.nb - 1) hcompare]
      cases hgallop : gallopLeft? afterB.state temp 0 left.key afterB.nb
        (afterB.nb - 1) with
      | none => rfl
      | some gallopB =>
        change
          (if gallopB.fuelExhausted then
            some (mergeHiFuelExhausted
              (eraseOccurrenceMergeHiCursor afterB))
            else _) =
            Option.map (eraseOccurrenceMergeHiResult)
              (if gallopB.fuelExhausted then
                some (mergeHiFuelExhausted afterB)
                else _)
        by_cases hfuel : gallopB.fuelExhausted = true
        · simp [hfuel]
        · simp only [hfuel, Bool.false_eq_true, if_false]
          simp only [eraseOccurrenceMergeHiCursor_state,
            eraseOccurrenceMergeHiCursor_dest, eraseOccurrenceMergeHiCursor_ssa,
            eraseOccurrenceMergeHiCursor_ssb, eraseOccurrenceMergeHiCursor_basea,
            eraseOccurrenceMergeHiCursor_na, eraseOccurrenceMergeHiCursor_nb,
            eraseOccurrenceMergeHiCursor_minGallop, eraseOccurrenceMergeHiCursor_phase]
          have hfinish (movedB : MergeHiCursor (Occurrence alpha) nu)
            (hmovedCompare : movedB.state.key_compare =
              occurrenceComparator lt) :
            (if movedB.nb = 0 ∨ movedB.nb = 1 then
              next' (eraseOccurrenceMergeHiCursor movedB)
              else
                Option.bind
                  (mergeHiCopyDataDecr?
                    (eraseOccurrenceMergeState movedB.state)
                    movedB.dest movedB.ssa) fun copiedA =>
                  let afterA : MergeHiCursor alpha nu :=
                    { eraseOccurrenceMergeHiCursor movedB with
                      state := copiedA.state
                      dest := copiedA.dst
                      ssa := copiedA.src
                      na := movedB.na - 1 }
                  if afterA.na = 0 then
                    next' afterA
                  else if mergeHiCountAtLeast aCount MIN_GALLOP ||
                    mergeHiCountAtLeast
                      (afterB.nb - gallopB.index) MIN_GALLOP then
                    next'
                      { afterA with
                        phase := .galloping aCount
                          (afterB.nb - gallopB.index) }
                  else
                    let minGallop := afterB.minGallop + 1
                    let state :=
                      { afterA.state with min_gallop := minGallop }
                    next'
                      { afterA with
                        state := state
                        minGallop := minGallop
                        phase := .straight 0 0 }) =
              Option.map (eraseOccurrenceMergeHiResult)
                (if movedB.nb = 0 ∨ movedB.nb = 1 then
                  next movedB
                  else
                    Option.bind
                      (mergeHiCopyDataDecr? movedB.state movedB.dest
                        movedB.ssa) fun copiedA =>
                      let afterA :
                        MergeHiCursor (Occurrence alpha) nu :=
                        { movedB with
                          state := copiedA.state
                          dest := copiedA.dst
                          ssa := copiedA.src
                          na := movedB.na - 1 }
                      if afterA.na = 0 then next afterA
                      else if mergeHiCountAtLeast aCount MIN_GALLOP ||
                        mergeHiCountAtLeast
                          (afterB.nb - gallopB.index) MIN_GALLOP then
                        next
                          { afterA with
                            phase := .galloping aCount
                              (afterB.nb - gallopB.index) }
                      else
                        let minGallop := afterB.minGallop + 1
                        let state :=
                          { afterA.state with min_gallop := minGallop }
                        next
                          { afterA with
                            state := state
                            minGallop := minGallop
                            phase := .straight 0 0 }) := by
            by_cases hsmall : movedB.nb = 0 ∨ movedB.nb = 1
            · simp only [hsmall, if_true]
              exact hnext movedB hmovedCompare
            · simp only [hsmall, if_false]
              rw [eraseOccurrenceMergeHiCopyDataDecr]
              cases hcopy : mergeHiCopyDataDecr? movedB.state
                movedB.dest movedB.ssa with
              | none => rfl
              | some copiedA =>
                simp only [Option.map_some, Option.bind_some]
                simp only [eraseOccurrenceMergeHiDataCursorResult]
                let afterA : MergeHiCursor (Occurrence alpha) nu :=
                  { movedB with
                    state := copiedA.state
                    dest := copiedA.dst
                    ssa := copiedA.src
                    na := movedB.na - 1 }
                have hafterCompare : afterA.state.key_compare =
                  occurrenceComparator lt := by
                  calc
                    afterA.state.key_compare =
                      movedB.state.key_compare :=
                      occurrenceErasure_mergeHiCopyDataDecr_key_compare_of_eq_some
                        movedB.state movedB.dest movedB.ssa copiedA hcopy
                    _ = occurrenceComparator lt := hmovedCompare
                change
                  (if afterA.na = 0 then
                    next' (eraseOccurrenceMergeHiCursor afterA)
                    else if mergeHiCountAtLeast aCount MIN_GALLOP ||
                      mergeHiCountAtLeast
                        (afterB.nb - gallopB.index) MIN_GALLOP then
                      next' (eraseOccurrenceMergeHiCursor
                        { afterA with
                          phase := .galloping aCount
                            (afterB.nb - gallopB.index) })
                    else _) =
                    Option.map (eraseOccurrenceMergeHiResult)
                      (if afterA.na = 0 then next afterA
                        else if mergeHiCountAtLeast aCount MIN_GALLOP ||
                          mergeHiCountAtLeast
                            (afterB.nb - gallopB.index) MIN_GALLOP then
                          next
                            { afterA with
                              phase := .galloping aCount
                                (afterB.nb - gallopB.index) }
                        else _)
                split
                · exact hnext afterA hafterCompare
                · split
                  · apply hnext
                    simpa using hafterCompare
                  · let minGallop := afterB.minGallop + 1
                    let adjustedState :=
                      { afterA.state with min_gallop := minGallop }
                    let adjusted :
                      MergeHiCursor (Occurrence alpha) nu :=
                      { afterA with
                        state := adjustedState
                        minGallop := minGallop
                        phase := .straight 0 0 }
                    change
                      next' (eraseOccurrenceMergeHiCursor adjusted) =
                        Option.map (eraseOccurrenceMergeHiResult)
                          (next adjusted)
                    apply hnext adjusted
                    simpa [adjusted, adjustedState] using hafterCompare
          by_cases hzero : afterB.nb - gallopB.index = 0
          · simp only [hzero, if_true]
            change
              (if afterB.nb = 0 ∨ afterB.nb = 1 then
                next' (eraseOccurrenceMergeHiCursor afterB)
                else
                  Option.bind
                    (mergeHiCopyDataDecr?
                      (eraseOccurrenceMergeState afterB.state)
                      afterB.dest afterB.ssa) _) =
                Option.map (eraseOccurrenceMergeHiResult)
                  (if afterB.nb = 0 ∨ afterB.nb = 1 then
                    next afterB
                    else
                      Option.bind
                        (mergeHiCopyDataDecr? afterB.state
                          afterB.dest afterB.ssa) _)
            simpa [hzero] using hfinish afterB hcompare
          · simp only [hzero, if_false]
            rw [eraseOccurrenceMergeHiGallopTempToData]
            cases hcopy : mergeHiMemcpyTempToData?
              .gallopTempToData rfl
              (afterB.nb - gallopB.index) afterB.state
              (afterB.dest - Int.ofNat
                (afterB.nb - gallopB.index) + 1)
              (afterB.ssb - Int.ofNat
                (afterB.nb - gallopB.index) + 1) with
            | none => rfl
            | some state =>
              simp only [Option.map_some]
              let movedB : MergeHiCursor (Occurrence alpha) nu :=
                { afterB with
                  state := state
                  dest := afterB.dest - Int.ofNat
                    (afterB.nb - gallopB.index)
                  ssb := afterB.ssb - Int.ofNat
                    (afterB.nb - gallopB.index)
                  nb := afterB.nb - (afterB.nb - gallopB.index) }
              change
                (if movedB.nb = 0 ∨ movedB.nb = 1 then
                  next' (eraseOccurrenceMergeHiCursor movedB)
                  else _) =
                  Option.map (eraseOccurrenceMergeHiResult)
                    (if movedB.nb = 0 ∨ movedB.nb = 1 then
                      next movedB
                      else _)
              apply hfinish movedB
              calc
                movedB.state.key_compare = afterB.state.key_compare :=
                  occurrenceErasure_mergeHiMemcpyTempToData_key_compare_of_eq_some
                    .gallopTempToData rfl
                    (afterB.nb - gallopB.index) afterB.state state
                    (afterB.dest - Int.ofNat
                      (afterB.nb - gallopB.index) + 1)
                    (afterB.ssb - Int.ofNat
                      (afterB.nb - gallopB.index) + 1) hcopy
                _ = occurrenceComparator lt := hcompare
set_option maxHeartbeats 2000000 in

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeHiGallopRound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeHiGallopRound
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {cursor : MergeHiCursor (Occurrence alpha) nu}
  {next : MergeHiCursor (Occurrence alpha) nu → Option (MergeHiResult (Occurrence alpha) nu)}
  {next' : MergeHiCursor alpha nu → Option (MergeHiResult alpha nu)}
-- given
  (hcompare : cursor.state.key_compare = occurrenceComparator lt)
  (hnext : ∀ cursor, cursor.state.key_compare = occurrenceComparator lt → next' (eraseOccurrenceMergeHiCursor cursor) = (next cursor).map (eraseOccurrenceMergeHiResult)) :
-- imply
  mergeHiGallopRound? (eraseOccurrenceMergeHiCursor cursor) next' = (mergeHiGallopRound? cursor next).map (eraseOccurrenceMergeHiResult) := by
-- proof
  unfold mergeHiGallopRound?
  simp only [eraseOccurrenceMergeHiCursor_state, eraseOccurrenceMergeHiCursor_dest,
    eraseOccurrenceMergeHiCursor_ssa, eraseOccurrenceMergeHiCursor_ssb,
    eraseOccurrenceMergeHiCursor_basea, eraseOccurrenceMergeHiCursor_na,
    eraseOccurrenceMergeHiCursor_nb, eraseOccurrenceMergeHiCursor_minGallop,
    eraseOccurrenceMergeHiCursor_phase, eraseOccurrenceMergeState_data,
    eraseOccurrenceMergeState_tempStorage]
  rw [expandedEraseOccurrenceMergeStateWithMinGallop]
  let minGallop := mergeHiDecreaseMinGallop cursor.minGallop
  let adjustedState : MergeState (Occurrence alpha) nu :=
    { cursor.state with min_gallop := minGallop }
  have hcompare' : adjustedState.key_compare = occurrenceComparator lt := by
    simpa [adjustedState] using hcompare
  change
    Option.bind
      (mergeHiTempRead? (eraseOccurrenceTempStorage adjustedState.a)
        cursor.ssb) _ =
      Option.map (eraseOccurrenceMergeHiResult)
        (Option.bind (mergeHiTempRead? adjustedState.a cursor.ssb) _)
  rw [eraseOccurrenceMergeHiTempRead]
  cases hright : mergeHiTempRead? adjustedState.a cursor.ssb with
  | none => rfl
  | some right =>
    simp only [Option.map_some, Option.bind_some,
      mergeHiBindOptionAcross]
    change
      mergeHiBindOptionAcross
        (gallopRight? (eraseOccurrenceMergeState adjustedState)
          (eraseOccurrenceSlice adjustedState.data) cursor.basea
          right.key.value cursor.na
          (cursor.na - 1)) _ =
        Option.map (eraseOccurrenceMergeHiResult)
          (mergeHiBindOptionAcross
            (gallopRight? adjustedState adjustedState.data cursor.basea
              right.key cursor.na (cursor.na - 1)) _)
    rw [eraseOccurrenceGallopRight lt adjustedState adjustedState.data
      cursor.basea right.key cursor.na (cursor.na - 1) hcompare']
    cases hgallop : gallopRight? adjustedState adjustedState.data
      cursor.basea right.key cursor.na (cursor.na - 1) with
    | none => rfl
    | some gallopA =>
      change
        (if gallopA.fuelExhausted then
          some (mergeHiFuelExhausted
            (eraseOccurrenceMergeHiCursor
              { cursor with state := adjustedState }))
          else _) =
          Option.map (eraseOccurrenceMergeHiResult)
            (if gallopA.fuelExhausted then
              some (mergeHiFuelExhausted
                { cursor with state := adjustedState })
              else _)
      by_cases hfuel : gallopA.fuelExhausted = true
      · simp [hfuel]
      · simp only [hfuel, Bool.false_eq_true, if_false]
        have hfinish (movedA : MergeHiCursor (Occurrence alpha) nu)
          (hmovedCompare : movedA.state.key_compare =
            occurrenceComparator lt) :
          (if movedA.na = 0 then
            next' (eraseOccurrenceMergeHiCursor movedA)
            else
              Option.bind
                (mergeHiCopyTempDecr?
                  (eraseOccurrenceMergeState movedA.state)
                  movedA.dest movedA.ssb) fun copiedB =>
                let afterB : MergeHiCursor alpha nu :=
                  { eraseOccurrenceMergeHiCursor movedA with
                    state := copiedB.state
                    dest := copiedB.dst
                    ssb := copiedB.src
                    nb := movedA.nb - 1 }
                if afterB.nb = 1 then
                  next' afterB
                else
                  mergeHiGallopB? afterB
                    (cursor.na - gallopA.index) next') =
            Option.map (eraseOccurrenceMergeHiResult)
              (if movedA.na = 0 then next movedA
                else
                  Option.bind
                    (mergeHiCopyTempDecr? movedA.state movedA.dest
                      movedA.ssb) fun copiedB =>
                    let afterB : MergeHiCursor (Occurrence alpha) nu :=
                      { movedA with
                        state := copiedB.state
                        dest := copiedB.dst
                        ssb := copiedB.src
                        nb := movedA.nb - 1 }
                    if afterB.nb = 1 then next afterB
                    else
                      mergeHiGallopB? afterB
                        (cursor.na - gallopA.index) next) := by
          by_cases hdone : movedA.na = 0
          · simp only [hdone, if_true]
            exact hnext movedA hmovedCompare
          · simp only [hdone, if_false]
            rw [eraseOccurrenceMergeHiCopyTempDecr]
            cases hcopy : mergeHiCopyTempDecr? movedA.state movedA.dest
              movedA.ssb with
            | none => rfl
            | some copiedB =>
              simp only [Option.map_some, Option.bind_some]
              simp only [eraseOccurrenceMergeHiDataCursorResult]
              let afterB : MergeHiCursor (Occurrence alpha) nu :=
                { movedA with
                  state := copiedB.state
                  dest := copiedB.dst
                  ssb := copiedB.src
                  nb := movedA.nb - 1 }
              have hafterCompare : afterB.state.key_compare =
                occurrenceComparator lt := by
                calc
                  afterB.state.key_compare = movedA.state.key_compare :=
                    occurrenceErasure_mergeHiCopyTempDecr_key_compare_of_eq_some
                      movedA.state movedA.dest movedA.ssb copiedB hcopy
                  _ = occurrenceComparator lt := hmovedCompare
              change
                (if afterB.nb = 1 then
                  next' (eraseOccurrenceMergeHiCursor afterB)
                  else
                    mergeHiGallopB?
                      (eraseOccurrenceMergeHiCursor afterB)
                      (cursor.na - gallopA.index) next') =
                  Option.map (eraseOccurrenceMergeHiResult)
                    (if afterB.nb = 1 then next afterB
                      else mergeHiGallopB? afterB
                        (cursor.na - gallopA.index) next)
              split
              · exact hnext afterB hafterCompare
              · exact eraseOccurrenceMergeHiGallopB lt afterB
                (cursor.na - gallopA.index) next next' hafterCompare
                hnext
        by_cases hzero : cursor.na - gallopA.index = 0
        · simp only [hzero, if_true]
          let movedA : MergeHiCursor (Occurrence alpha) nu :=
            { cursor with state := adjustedState, minGallop := minGallop }
          change
            (if movedA.na = 0 then
              next' (eraseOccurrenceMergeHiCursor movedA)
              else _) =
              Option.map (eraseOccurrenceMergeHiResult)
                (if movedA.na = 0 then next movedA else _)
          simpa [movedA, adjustedState, minGallop, hzero] using
            hfinish movedA hcompare'
        · simp only [hzero, if_false]
          rw [eraseOccurrenceMergeDataMemmove]
          cases hmove : mergeDataMemmove? .hiGallopA adjustedState.data
            (cursor.dest - Int.ofNat (cursor.na - gallopA.index) + 1)
            (cursor.ssa - Int.ofNat (cursor.na - gallopA.index) + 1)
            (cursor.na - gallopA.index) with
          | none => rfl
          | some data =>
            simp only [Option.map_some]
            let movedA : MergeHiCursor (Occurrence alpha) nu :=
              { cursor with
                state := { adjustedState with data := data }
                dest := cursor.dest - Int.ofNat
                  (cursor.na - gallopA.index)
                ssa := cursor.ssa - Int.ofNat
                  (cursor.na - gallopA.index)
                na := cursor.na - (cursor.na - gallopA.index)
                minGallop := minGallop }
            change
              (if movedA.na = 0 then
                next' (eraseOccurrenceMergeHiCursor movedA)
                else _) =
                Option.map (eraseOccurrenceMergeHiResult)
                  (if movedA.na = 0 then next movedA else _)
            apply hfinish movedA
            simpa [movedA] using hcompare'
set_option maxHeartbeats 2000000 in

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeHiLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeHiLoop
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {fuel : Nat}
  {cursor : MergeHiCursor (Occurrence alpha) nu}
-- given
  (hcompare : cursor.state.key_compare = occurrenceComparator lt) :
-- imply
  mergeHiLoop? fuel (eraseOccurrenceMergeHiCursor cursor) = (mergeHiLoop? fuel cursor).map (eraseOccurrenceMergeHiResult) := by
-- proof
  induction fuel generalizing cursor with
  | zero =>
    simp only [mergeHiLoop?, eraseOccurrenceMergeHiCursor_na,
      eraseOccurrenceMergeHiCursor_nb]
    by_cases hdone : cursor.na = 0 ∨ cursor.nb = 0
    · simp only [hdone, if_true]
      exact eraseOccurrenceMergeHiSucceed cursor
    · simp only [hdone, if_false]
      by_cases hone : cursor.nb = 1
      · simp only [hone, if_true]
        exact eraseOccurrenceMergeHiCopyA cursor
      · simp only [hone, if_false]
        exact congrArg some (eraseOccurrenceMergeHiFuelExhausted cursor)
  | succ fuel ih =>
    simp only [mergeHiLoop?, eraseOccurrenceMergeHiCursor_na,
      eraseOccurrenceMergeHiCursor_nb, eraseOccurrenceMergeHiCursor_phase,
      eraseOccurrenceMergeHiCursor_state, eraseOccurrenceMergeHiCursor_dest,
      eraseOccurrenceMergeHiCursor_ssa, eraseOccurrenceMergeHiCursor_ssb,
      eraseOccurrenceMergeHiCursor_basea, eraseOccurrenceMergeHiCursor_minGallop]
    by_cases hdone : cursor.na = 0 ∨ cursor.nb = 0
    · simp only [hdone, if_true]
      exact eraseOccurrenceMergeHiSucceed cursor
    · simp only [hdone, if_false]
      by_cases hone : cursor.nb = 1
      · simp only [hone, if_true]
        exact eraseOccurrenceMergeHiCopyA cursor
      · simp only [hone, if_false]
        cases hphase : cursor.phase with
        | straight aCount bCount =>
          rw [eraseOccurrenceMergeState_tempStorage, eraseOccurrenceMergeHiTempRead]
          cases hright : mergeHiTempRead? cursor.state.a cursor.ssb with
          | none => rfl
          | some right =>
            simp only [Option.map_some, bind, Option.bind]
            rw [eraseOccurrenceMergeState_data, eraseOccurrenceSlice_read]
            cases hleft : cursor.state.data.read? cursor.ssa with
            | none => rfl
            | some left =>
              simp only [Option.map_some,
                eraseOccurrenceMergeState_key_compare, hcompare,
                eraseOccurrenceComparator_occurrenceComparator,
                eraseOccurrenceEntry_key, iflt_eraseOccurrence]
              split
              · rw [eraseOccurrenceMergeHiCopyDataDecr]
                cases hcopy : mergeHiCopyDataDecr? cursor.state
                  cursor.dest cursor.ssa with
                | none => rfl
                | some copied =>
                  simp only [Option.map_some,
                    eraseOccurrenceMergeHiDataCursorResult]
                  let nextCursor :
                    MergeHiCursor (Occurrence alpha) nu :=
                    { cursor with
                      state := copied.state
                      dest := copied.dst
                      ssa := copied.src
                      na := cursor.na - 1
                      phase :=
                        if mergeHiCountAtLeast (aCount + 1)
                          cursor.minGallop then
                          .galloping (aCount + 1) 0
                        else
                          .straight (aCount + 1) 0
                      minGallop :=
                        if mergeHiCountAtLeast (aCount + 1)
                          cursor.minGallop then
                          cursor.minGallop + 1
                        else
                          cursor.minGallop }
                  change
                    mergeHiLoop? fuel
                      (eraseOccurrenceMergeHiCursor nextCursor) =
                      Option.map (eraseOccurrenceMergeHiResult)
                        (mergeHiLoop? fuel nextCursor)
                  apply ih nextCursor
                  calc
                    nextCursor.state.key_compare =
                      cursor.state.key_compare :=
                      occurrenceErasure_mergeHiCopyDataDecr_key_compare_of_eq_some
                        cursor.state cursor.dest cursor.ssa copied
                        hcopy
                    _ = occurrenceComparator lt := hcompare
              · rw [eraseOccurrenceMergeHiCopyTempDecr]
                cases hcopy : mergeHiCopyTempDecr? cursor.state
                  cursor.dest cursor.ssb with
                | none => rfl
                | some copied =>
                  simp only [Option.map_some,
                    eraseOccurrenceMergeHiDataCursorResult]
                  let nextCursor :
                    MergeHiCursor (Occurrence alpha) nu :=
                    { cursor with
                      state := copied.state
                      dest := copied.dst
                      ssb := copied.src
                      nb := cursor.nb - 1
                      phase :=
                        if mergeHiCountAtLeast (bCount + 1)
                          cursor.minGallop then
                          .galloping 0 (bCount + 1)
                        else
                          .straight 0 (bCount + 1)
                      minGallop :=
                        if mergeHiCountAtLeast (bCount + 1)
                          cursor.minGallop then
                          cursor.minGallop + 1
                        else
                          cursor.minGallop }
                  change
                    mergeHiLoop? fuel
                      (eraseOccurrenceMergeHiCursor nextCursor) =
                      Option.map (eraseOccurrenceMergeHiResult)
                        (mergeHiLoop? fuel nextCursor)
                  apply ih nextCursor
                  calc
                    nextCursor.state.key_compare =
                      cursor.state.key_compare :=
                      occurrenceErasure_mergeHiCopyTempDecr_key_compare_of_eq_some
                        cursor.state cursor.dest cursor.ssb copied
                        hcopy
                    _ = occurrenceComparator lt := hcompare
        | galloping aCount bCount =>
          exact eraseOccurrenceMergeHiGallopRound lt cursor
            (mergeHiLoop? fuel) (mergeHiLoop? fuel) hcompare
            (fun nextCursor hnextCompare =>
              ih nextCursor hnextCompare)

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeHi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
lemma eraseOccurrenceMergeHi
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {state : MergeState (Occurrence alpha) nu}
  {ssa ssb : Int}
  {na nb : Nat}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  mergeHi? (eraseOccurrenceMergeState state) ssa ssb na nb = (mergeHi? state ssa ssb na nb).map (eraseOccurrenceMergeHiResult) := by
-- proof
  unfold mergeHi?
  split <;> try rfl
  rw [eraseOccurrenceMergeGetmem]
  cases hallocated : mergeGetmem state (BitVec.ofNat 64 nb) with
  | mk allocatedState outcome =>
    cases outcome with
    | guardRejected =>
      simp [eraseOccurrenceMergeGetmemResult, eraseOccurrenceMergeHiResult]
    | reused =>
      simp only [eraseOccurrenceMergeGetmemResult]
      rw [eraseOccurrenceMergeHiInitialDataToTemp]
      cases hcopy : mergeHiMemcpyDataToTemp? .initialDataToTemp rfl nb
        allocatedState 0 ssb with
      | none => rfl
      | some copiedState =>
        simp only [Option.map_some, bind, Option.bind]
        let initial : MergeState (Occurrence alpha) nu := copiedState
        rw [eraseOccurrenceMergeHiCopyDataDecr]
        cases hfirst : mergeHiCopyDataDecr? initial
          (ssb + Int.ofNat (nb - 1))
          (ssa + Int.ofNat (na - 1)) with
        | none => rfl
        | some copied =>
          simp only [Option.map_some,
            eraseOccurrenceMergeHiDataCursorResult]
          let cursor : MergeHiCursor (Occurrence alpha) nu :=
            { state := copied.state
              dest := copied.dst
              ssa := copied.src
              ssb := Int.ofNat (nb - 1)
              basea := ssa
              na := na - 1
              nb := nb
              minGallop := copied.state.min_gallop
              phase := .straight 0 0 }
          have hallocatedCompare : allocatedState.key_compare =
            state.key_compare := by
            have hframe := mergeGetmem_key_compare state
              (BitVec.ofNat 64 nb)
            simpa [hallocated] using hframe
          have hcursorCompare : cursor.state.key_compare =
            occurrenceComparator lt := by
            calc
              cursor.state.key_compare = initial.key_compare :=
                occurrenceErasure_mergeHiCopyDataDecr_key_compare_of_eq_some initial
                  (ssb + Int.ofNat (nb - 1))
                  (ssa + Int.ofNat (na - 1)) copied hfirst
              _ = copiedState.key_compare := rfl
              _ = allocatedState.key_compare :=
                occurrenceErasure_mergeHiMemcpyDataToTemp_key_compare_of_eq_some
                  .initialDataToTemp rfl nb allocatedState copiedState
                  0 ssb hcopy
              _ = state.key_compare := hallocatedCompare
              _ = occurrenceComparator lt := hcompare
          change
            mergeHiLoop? (na + nb)
              (eraseOccurrenceMergeHiCursor cursor) =
              Option.map (eraseOccurrenceMergeHiResult)
                (mergeHiLoop? (na + nb) cursor)
          exact eraseOccurrenceMergeHiLoop lt (na + nb) cursor
            hcursorCompare
    | grown =>
      simp only [eraseOccurrenceMergeGetmemResult]
      rw [eraseOccurrenceMergeHiInitialDataToTemp]
      cases hcopy : mergeHiMemcpyDataToTemp? .initialDataToTemp rfl nb
        allocatedState 0 ssb with
      | none => rfl
      | some copiedState =>
        simp only [Option.map_some, bind, Option.bind]
        let initial : MergeState (Occurrence alpha) nu := copiedState
        rw [eraseOccurrenceMergeHiCopyDataDecr]
        cases hfirst : mergeHiCopyDataDecr? initial
          (ssb + Int.ofNat (nb - 1))
          (ssa + Int.ofNat (na - 1)) with
        | none => rfl
        | some copied =>
          simp only [Option.map_some,
            eraseOccurrenceMergeHiDataCursorResult]
          let cursor : MergeHiCursor (Occurrence alpha) nu :=
            { state := copied.state
              dest := copied.dst
              ssa := copied.src
              ssb := Int.ofNat (nb - 1)
              basea := ssa
              na := na - 1
              nb := nb
              minGallop := copied.state.min_gallop
              phase := .straight 0 0 }
          have hallocatedCompare : allocatedState.key_compare =
            state.key_compare := by
            have hframe := mergeGetmem_key_compare state
              (BitVec.ofNat 64 nb)
            simpa [hallocated] using hframe
          have hcursorCompare : cursor.state.key_compare =
            occurrenceComparator lt := by
            calc
              cursor.state.key_compare = initial.key_compare :=
                occurrenceErasure_mergeHiCopyDataDecr_key_compare_of_eq_some initial
                  (ssb + Int.ofNat (nb - 1))
                  (ssa + Int.ofNat (na - 1)) copied hfirst
              _ = copiedState.key_compare := rfl
              _ = allocatedState.key_compare :=
                occurrenceErasure_mergeHiMemcpyDataToTemp_key_compare_of_eq_some
                  .initialDataToTemp rfl nb allocatedState copiedState
                  0 ssb hcopy
              _ = state.key_compare := hallocatedCompare
              _ = occurrenceComparator lt := hcompare
          change
            mergeHiLoop? (na + nb)
              (eraseOccurrenceMergeHiCursor cursor) =
              Option.map (eraseOccurrenceMergeHiResult)
                (mergeHiLoop? (na + nb) cursor)
          exact eraseOccurrenceMergeHiLoop lt (na + nb) cursor
            hcursorCompare

end CPythonListsort

/--
[eraseOccurrenceMergeLoResult_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
private lemma eraseOccurrenceMergeLoResult_state_eq
  {alpha : Type u}
  {nu : Type v}
  {result : MergeLoResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeLoResult result).state = eraseOccurrenceMergeState result.state := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeLoResult_state result

/--
[eraseOccurrenceMergeLoMachine_na](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
private lemma eraseOccurrenceMergeLoMachine_na_eq
  {alpha : Type u}
  {nu : Type v}
  {machine : MergeLoMachine (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeLoMachine machine).na = machine.na := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeLoMachine_na machine

/--
[eraseOccurrenceMergeLoMachine_nb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
private lemma eraseOccurrenceMergeLoMachine_nb_eq
  {alpha : Type u}
  {nu : Type v}
  {machine : MergeLoMachine (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeLoMachine machine).nb = machine.nb := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeLoMachine_nb machine

/--
[eraseOccurrenceMergeHiCursor_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
private lemma eraseOccurrenceMergeHiCursor_state_eq
  {alpha : Type u}
  {nu : Type v}
  {cursor : MergeHiCursor (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeHiCursor cursor).state = eraseOccurrenceMergeState cursor.state := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeHiCursor_state cursor

/--
[eraseOccurrenceMergeHiCursor_dest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
private lemma eraseOccurrenceMergeHiCursor_dest_eq
  {alpha : Type u}
  {nu : Type v}
  {cursor : MergeHiCursor (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeHiCursor cursor).dest = cursor.dest := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeHiCursor_dest cursor

/--
[eraseOccurrenceMergeHiCursor_ssa](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
private lemma eraseOccurrenceMergeHiCursor_ssa_eq
  {alpha : Type u}
  {nu : Type v}
  {cursor : MergeHiCursor (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeHiCursor cursor).ssa = cursor.ssa := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeHiCursor_ssa cursor

/--
[eraseOccurrenceMergeHiCursor_ssb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
private lemma eraseOccurrenceMergeHiCursor_ssb_eq
  {alpha : Type u}
  {nu : Type v}
  {cursor : MergeHiCursor (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeHiCursor cursor).ssb = cursor.ssb := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeHiCursor_ssb cursor

/--
[eraseOccurrenceMergeHiCursor_basea](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
private lemma eraseOccurrenceMergeHiCursor_basea_eq
  {alpha : Type u}
  {nu : Type v}
  {cursor : MergeHiCursor (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeHiCursor cursor).basea = cursor.basea := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeHiCursor_basea cursor

/--
[eraseOccurrenceMergeHiCursor_na](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
private lemma eraseOccurrenceMergeHiCursor_na_eq
  {alpha : Type u}
  {nu : Type v}
  {cursor : MergeHiCursor (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeHiCursor cursor).na = cursor.na := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeHiCursor_na cursor

/--
[eraseOccurrenceMergeHiCursor_nb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
private lemma eraseOccurrenceMergeHiCursor_nb_eq
  {alpha : Type u}
  {nu : Type v}
  {cursor : MergeHiCursor (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeHiCursor cursor).nb = cursor.nb := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeHiCursor_nb cursor

/--
[eraseOccurrenceMergeHiCursor_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean)
-/
@[path]
private lemma eraseOccurrenceMergeHiCursor_phase_eq
  {alpha : Type u}
  {nu : Type v}
  {cursor : MergeHiCursor (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeHiCursor cursor).phase = cursor.phase := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeHiCursor_phase cursor


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Def.CPythonListsort.Code.Transcription.MergeLo.Part6
open CPythonListsort


namespace CPythonListsort

/--
[mergeLoTempWrite_eq_some_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLoTempWrite_eq_some_of_lt
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {index : Nat}
  {entry : SortSliceEntry κ ν}
-- given
  (hindex : index < storage.cells.size) :
-- imply
  mergeLoTempWrite? storage index entry = some { storage with cells := storage.cells.set index (some entry) } := by
-- proof
  simp [mergeLoTempWrite?, hindex]

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoTempWrite_eq_none_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLoTempWrite_eq_none_of_le
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {index : Nat}
  {entry : SortSliceEntry κ ν}
-- given
  (hindex : storage.cells.size ≤ index) :
-- imply
  mergeLoTempWrite? storage index entry = none := by
-- proof
  simp [mergeLoTempWrite?, Nat.not_lt.mpr hindex]

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoTempRead_write_self_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLoTempRead_write_self_of_eq_some
  {κ : Type u}
  {ν : Type v}
  {storage updated : TempStorage κ ν}
  {index : Nat}
  {entry : SortSliceEntry κ ν}
-- given
  (hwrite : mergeLoTempWrite? storage index entry = some updated) :
-- imply
  mergeLoTempRead? updated index = some entry := by
-- proof
  simp only [mergeLoTempWrite?] at hwrite
  split at hwrite
  · injection hwrite with hwrite
    subst updated
    simp [mergeLoTempRead?]
  · simp at hwrite

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoTempRead_write_ne_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLoTempRead_write_ne_of_eq_some
  {κ : Type u}
  {ν : Type v}
  {storage updated : TempStorage κ ν}
  {index other : Nat}
  {entry : SortSliceEntry κ ν}
-- given
  (hwrite : mergeLoTempWrite? storage index entry = some updated)
  (hne : other ≠ index) :
-- imply
  mergeLoTempRead? updated other = mergeLoTempRead? storage other := by
-- proof
  simp only [mergeLoTempWrite?] at hwrite
  split at hwrite
  · injection hwrite with hwrite
    subst updated
    simp only [mergeLoTempRead?, bind, Option.bind]
    rw [Array.getElem?_set_ne _ hne.symm]
  · simp at hwrite

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoMemcpyDataToTemp_read_before_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLoMemcpyDataToTemp_read_before_of_eq_some
  {κ : Type u}
  {ν : Type v}
  {site : MergeLoMemcpyCallsite}
  {count : Nat}
  {state state' : MergeState κ ν}
  {destination : Nat}
  {source : Int}
  {other : Nat}
-- given
  (hDirection : site.backings = { destination := .temporary, source := .main })
  (hresult : mergeLoMemcpyDataToTemp? site hDirection count state destination source = some state')
  (hother : other < destination) :
-- imply
  mergeLoTempRead? state'.a other = mergeLoTempRead? state.a other := by
-- proof
  induction count generalizing state destination source with
  | zero =>
    simp only [mergeLoMemcpyDataToTemp?] at hresult
    injection hresult with hresult
    subst state'
    rfl
  | succ count ih =>
    cases hread : state.data.read? source with
    | none => simp [mergeLoMemcpyDataToTemp?, hread] at hresult
    | some entry =>
      cases hwrite : mergeLoTempWrite? state.a destination entry with
      | none =>
        simp [mergeLoMemcpyDataToTemp?, hread, hwrite] at hresult
      | some storage =>
        have htail :
          mergeLoMemcpyDataToTemp? site hDirection count
            { state with a := storage } (destination + 1) (source + 1) =
              some state' := by
          simpa [mergeLoMemcpyDataToTemp?, hread, hwrite] using hresult
        have hrecursive :=
          ih { state with a := storage } (destination + 1) (source + 1)
            htail (by omega)
        have hwriteFrame :=
          mergeLoTempRead_write_ne_of_eq_some state.a storage destination
            other entry hwrite (Nat.ne_of_lt hother)
        exact hrecursive.trans hwriteFrame

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoMemcpyDataToTemp_initialized_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLoMemcpyDataToTemp_initialized_of_eq_some
  {κ : Type u}
  {ν : Type v}
  {site : MergeLoMemcpyCallsite}
  {count : Nat}
  {state state' : MergeState κ ν}
  {destination : Nat}
  {source : Int}
-- given
  (hDirection : site.backings = { destination := .temporary, source := .main })
  (hresult : mergeLoMemcpyDataToTemp? site hDirection count state destination source = some state') :
-- imply
  MergeLoTempRangeInitialized state'.a destination count := by
-- proof
  induction count generalizing state destination source with
  | zero =>
    intro i hi
    omega
  | succ count ih =>
    cases hread : state.data.read? source with
    | none => simp [mergeLoMemcpyDataToTemp?, hread] at hresult
    | some entry =>
      cases hwrite : mergeLoTempWrite? state.a destination entry with
      | none =>
        simp [mergeLoMemcpyDataToTemp?, hread, hwrite] at hresult
      | some storage =>
        have htail :
          mergeLoMemcpyDataToTemp? site hDirection count
            { state with a := storage } (destination + 1) (source + 1) =
              some state' := by
          simpa [mergeLoMemcpyDataToTemp?, hread, hwrite] using hresult
        have htailInitialized :=
          ih { state with a := storage } (destination + 1) (source + 1)
            htail
        intro i hi
        cases i with
        | zero =>
          have hpreserved :=
            mergeLoMemcpyDataToTemp_read_before_of_eq_some site
              hDirection count { state with a := storage } state'
              (destination + 1) (source + 1) htail destination (by omega)
          have hinitialized :=
            mergeLoTempRead_write_self_of_eq_some state.a storage
              destination entry hwrite
          exact ⟨entry, by simpa using hpreserved.trans hinitialized⟩
        | succ i =>
          have hiTail : i < count := by omega
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            htailInitialized i hiTail

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoGatherTempEntries_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLoGatherTempEntries_spec
  {κ : Type u}
  {ν : Type v}
  {count : Nat}
  {storage : TempStorage κ ν}
  {source : Nat}
  {initial result : Array (SortSliceEntry κ ν)}
-- given
  (hresult : mergeLoGatherTempEntries? count storage source initial = some result) :
-- imply
  result.size = initial.size + count ∧ (∀ i < initial.size, result[i]? = initial[i]?) ∧ ∀ i < count, result[initial.size + i]? = storage.cells[source + i]?.bind id := by
-- proof
  induction count generalizing source initial with
  | zero =>
    simp only [mergeLoGatherTempEntries?] at hresult
    injection hresult with hresult
    subst result
    simp
  | succ count ih =>
    cases hcell : storage.cells[source]? with
    | none => simp [mergeLoGatherTempEntries?, mergeLoTempRead?, hcell] at hresult
    | some cell =>
      cases cell with
      | none => simp [mergeLoGatherTempEntries?, mergeLoTempRead?, hcell] at hresult
      | some entry =>
        have hnext :
          mergeLoGatherTempEntries? count storage (source + 1)
            (initial.push entry) = some result := by
          simpa [mergeLoGatherTempEntries?, mergeLoTempRead?, hcell] using hresult
        rcases ih (source + 1) (initial.push entry) hnext with
          ⟨hsize, hprefix, hgathered⟩
        refine ⟨by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hsize, ?_, ?_⟩
        · intro i hi
          have hpreserved := hprefix i (by
            simpa using Nat.lt_succ_of_lt hi)
          simpa [Array.getElem?_push, Nat.ne_of_lt hi] using hpreserved
        · intro i hi
          cases i with
          | zero =>
            have hnew := hprefix initial.size (by simp)
            simpa [Array.getElem?_push, hcell] using hnew
          | succ i =>
            have hiCount : i < count := by omega
            have hrest := hgathered i hiCount
            simpa [Array.size_push, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using hrest

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoGatherTempEntries_exists_of_initialized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLoGatherTempEntries_exists_of_initialized
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {source count : Nat}
  {initial : Array (SortSliceEntry κ ν)}
-- given
  (hinitialized : MergeLoTempRangeInitialized storage source count) :
-- imply
  ∃ result, mergeLoGatherTempEntries? count storage source initial = some result := by
-- proof
  induction count generalizing source initial with
  | zero =>
    exact ⟨initial, rfl⟩
  | succ count ih =>
    obtain ⟨entry, hentry⟩ := hinitialized 0 (by omega)
    have htail : MergeLoTempRangeInitialized storage (source + 1) count := by
      intro i hi
      have := hinitialized (i + 1) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
    rcases ih (source + 1) (initial.push entry) htail with
      ⟨result, hresult⟩
    have hentry' : mergeLoTempRead? storage source = some entry := by
      simpa using hentry
    refine ⟨result, ?_⟩
    simp only [mergeLoGatherTempEntries?]
    rwa [hentry']

end CPythonListsort

namespace CPythonListsort

/--
[tempRun_cells_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma tempRun_cells_of_eq_some
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {source count : Nat}
  {slice : SortSlice κ ν}
-- given
  (hresult : tempRun? storage source count = some slice) :
-- imply
  slice.entries.size = count ∧ ∀ i < count, storage.cells[source + i]?.bind id = slice.entries[i]? := by
-- proof
  unfold tempRun? mergeLoTempRun? at hresult
  cases hentries : mergeLoGatherTempEntries? count storage source #[] with
  | none => simp [hentries] at hresult
  | some entries =>
    have hmaterialized :
      (some ({ entries := entries } : SortSlice κ ν)) = some slice := by
      simpa [hentries] using hresult
    injection hmaterialized with hmaterialized
    subst slice
    rcases mergeLoGatherTempEntries_spec count storage source #[] entries hentries with
      ⟨hsize, _hprefix, hrange⟩
    exact ⟨by simpa using hsize, fun i hi => by
      simpa using (hrange i hi).symm⟩

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoTempRun_cells_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLoTempRun_cells_of_eq_some
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {source count : Nat}
  {slice : SortSlice κ ν}
-- given
  (hresult : mergeLoTempRun? storage source count = some slice) :
-- imply
  slice.entries.size = count ∧ ∀ i < count, storage.cells[source + i]?.bind id = slice.entries[i]? :=
-- proof
  tempRun_cells_of_eq_some storage source count slice hresult

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoTempRun_exists_of_initialized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLoTempRun_exists_of_initialized
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {source count : Nat}
-- given
  (hinitialized : MergeLoTempRangeInitialized storage source count) :
-- imply
  ∃ slice, mergeLoTempRun? storage source count = some slice := by
-- proof
  rcases mergeLoGatherTempEntries_exists_of_initialized storage source count #[]
    hinitialized with ⟨entries, hentries⟩
  refine ⟨{ entries := entries }, ?_⟩
  simp [mergeLoTempRun?, hentries]

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoTempRun_initialized_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLoTempRun_initialized_of_eq_some
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {source count : Nat}
  {slice : SortSlice κ ν}
-- given
  (hresult : mergeLoTempRun? storage source count = some slice) :
-- imply
  MergeLoTempRangeInitialized storage source count := by
-- proof
  rcases tempRun_cells_of_eq_some storage source count slice hresult with
    ⟨hsize, hcells⟩
  intro i hi
  have hiSize : i < slice.entries.size := by omega
  refine ⟨slice.entries[i], ?_⟩
  have hcell := hcells i hi
  rw [Array.getElem?_eq_getElem hiSize] at hcell
  simpa [mergeLoTempRead?] using hcell

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoTempRun_exists_iff_initialized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLoTempRun_exists_iff_initialized
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {source count : Nat} :
-- imply
  (∃ slice, mergeLoTempRun? storage source count = some slice) ↔ MergeLoTempRangeInitialized storage source count := by
-- proof
  constructor
  · rintro ⟨slice, hslice⟩
    exact mergeLoTempRun_initialized_of_eq_some storage source count slice hslice
  · exact mergeLoTempRun_exists_of_initialized storage source count

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoCopyAIncr_equation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLoCopyAIncr_equation
  {κ : Type u}
  {ν : Type v}
  {machine : MergeLoMachine κ ν} :
-- imply
  mergeLoCopyAIncr? machine = (do let entry ← mergeLoTempRead? machine.state.a machine.aPos let data ← machine.state.data.write? machine.dest entry pure { machine with state := { machine.state with data := data } dest := machine.dest + 1 aPos := machine.aPos + 1 na := machine.na - 1 }) := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoCopyBIncr_equation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLoCopyBIncr_equation
  {κ : Type u}
  {ν : Type v}
  {machine : MergeLoMachine κ ν} :
-- imply
  mergeLoCopyBIncr? machine = (do let entry ← machine.state.data.read? machine.bPos let data ← machine.state.data.write? machine.dest entry pure { machine with state := { machine.state with data := data } dest := machine.dest + 1 bPos := machine.bPos + 1 nb := machine.nb - 1 }) := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoCopyB_memmove_equation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLoCopyB_memmove_equation
  {κ : Type u}
  {ν : Type v}
  {machine : MergeLoMachine κ ν} :
-- imply
  mergeLoCopyB? machine = (do if machine.na = 1 ∧ 0 < machine.nb then let data ← mergeDataMemmove? .loCopyBTail machine.state.data machine.dest machine.bPos machine.nb let state := { machine.state with data := data } let entry ← mergeLoTempRead? state.a machine.aPos let data ← state.data.write? (machine.dest + Int.ofNat machine.nb) entry pure (mergeLoSuccess { state with data := data }) else none) := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoGallopRound_equation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLoGallopRound_equation
  {κ : Type u}
  {ν : Type v}
  {machine : MergeLoMachine κ ν}
  {next : MergeLoMachine κ ν → Nat → Nat → Option (MergeLoResult κ ν)} :
-- imply
  mergeLoGallopRound? machine next = (do if machine.na ≤ 1 ∨ machine.nb = 0 then none else let minGallop := if (1 : PySSize).slt machine.minGallop then machine.minGallop - 1 else machine.minGallop let state := { machine.state with min_gallop := minGallop } let machine := { machine with state := state, minGallop := minGallop } let firstB ← machine.state.data.read? machine.bPos let activeA ← mergeLoTempRun? machine.state.a machine.aPos machine.na mergeLoBindOptionAcross (gallopRight? machine.state activeA 0 firstB.key machine.na 0) fun gallopA => if gallopA.fuelExhausted then mergeLoGallopFuelFailure machine else let aCount := gallopA.index if aCount > machine.na then none else do let state ← mergeLoMemcpyTempToData? .gallopTempToData rfl aCount machine.state machine.dest machine.aPos let machine : MergeLoMachine κ ν := { machine with state := state dest := machine.dest + Int.ofNat aCount aPos := machine.aPos + aCount na := machine.na - aCount } if machine.na = 0 then mergeLoSucceed? machine else if machine.na = 1 then mergeLoCopyB? machine else let machine ← mergeLoCopyBIncr? machine if machine.nb = 0 then mergeLoSucceed? machine else let firstA ← mergeLoTempRead? machine.state.a machine.aPos mergeLoBindOptionAcross (gallopLeft? machine.state machine.state.data machine.bPos firstA.key machine.nb 0) fun gallopB => if gallopB.fuelExhausted then mergeLoGallopFuelFailure machine else let bCount := gallopB.index if bCount > machine.nb then none else do let data ← mergeDataMemmove? .loGallopB machine.state.data machine.dest machine.bPos bCount let machine : MergeLoMachine κ ν := { machine with state := { machine.state with data := data } dest := machine.dest + Int.ofNat bCount bPos := machine.bPos + Int.ofNat bCount nb := machine.nb - bCount } if machine.nb = 0 then mergeLoSucceed? machine else let machine ← mergeLoCopyAIncr? machine if machine.na = 1 then mergeLoCopyB? machine else next machine aCount bCount) := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoLoop_ordinary_copyB_equation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLoLoop_ordinary_copyB_equation
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {machine : MergeLoMachine κ ν}
  {aCount bCount : Nat}
  {firstA firstB : SortSliceEntry κ ν}
-- given
  (hactive : ¬ (machine.na ≤ 1 ∨ machine.nb = 0))
  (hfirstA : mergeLoTempRead? machine.state.a machine.aPos = some firstA)
  (hfirstB : machine.state.data.read? machine.bPos = some firstB)
  (hcompare : machine.state.key_compare firstB.key firstA.key = true) :
-- imply
  mergeLoLoop? (fuel + 1) machine (.ordinary aCount bCount) = (do let machine ← mergeLoCopyBIncr? machine let bCount := bCount + 1 if machine.nb = 0 then mergeLoSucceed? machine else if mergeLoCountAtLeastWord bCount machine.minGallop then mergeLoLoop? fuel { machine with minGallop := machine.minGallop + 1 } .galloping else mergeLoLoop? fuel machine (.ordinary 0 bCount)) := by
-- proof
  rw [mergeLoLoop?]
  simp [hactive, hfirstA, hfirstB, iflt, hcompare]

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoLoop_ordinary_copyA_equation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLoLoop_ordinary_copyA_equation
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {machine : MergeLoMachine κ ν}
  {aCount bCount : Nat}
  {firstA firstB : SortSliceEntry κ ν}
-- given
  (hactive : ¬ (machine.na ≤ 1 ∨ machine.nb = 0))
  (hfirstA : mergeLoTempRead? machine.state.a machine.aPos = some firstA)
  (hfirstB : machine.state.data.read? machine.bPos = some firstB)
  (hcompare : machine.state.key_compare firstB.key firstA.key = false) :
-- imply
  mergeLoLoop? (fuel + 1) machine (.ordinary aCount bCount) = (do let machine ← mergeLoCopyAIncr? machine let aCount := aCount + 1 if machine.na = 1 then mergeLoCopyB? machine else if mergeLoCountAtLeastWord aCount machine.minGallop then mergeLoLoop? fuel { machine with minGallop := machine.minGallop + 1 } .galloping else mergeLoLoop? fuel machine (.ordinary aCount 0)) := by
-- proof
  rw [mergeLoLoop?]
  simp [hactive, hfirstA, hfirstB, iflt, hcompare]

end CPythonListsort

namespace CPythonListsort

/--
[mergeLoLoop_ordinary_equal_keys_equation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLoLoop_ordinary_equal_keys_equation
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {machine : MergeLoMachine κ ν}
  {aCount bCount : Nat}
  {firstA firstB : SortSliceEntry κ ν}
-- given
  (hactive : ¬ (machine.na ≤ 1 ∨ machine.nb = 0))
  (hfirstA : mergeLoTempRead? machine.state.a machine.aPos = some firstA)
  (hfirstB : machine.state.data.read? machine.bPos = some firstB)
  (hkeys : firstB.key = firstA.key)
  (hirrefl : machine.state.key_compare firstA.key firstA.key = false) :
-- imply
  mergeLoLoop? (fuel + 1) machine (.ordinary aCount bCount) = (do let machine ← mergeLoCopyAIncr? machine let aCount := aCount + 1 if machine.na = 1 then mergeLoCopyB? machine else if mergeLoCountAtLeastWord aCount machine.minGallop then mergeLoLoop? fuel { machine with minGallop := machine.minGallop + 1 } .galloping else mergeLoLoop? fuel machine (.ordinary aCount 0)) := by
-- proof
  apply mergeLoLoop_ordinary_copyA_equation fuel machine aCount bCount
    firstA firstB hactive hfirstA hfirstB
  simpa [hkeys] using hirrefl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[dataWrite_layout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
private lemma dataWrite_layout (state : MergeState κ ν)
  (updated : SortSlice κ ν) (index : Int) (entry : SortSliceEntry κ ν)
  (h : state.data.write? index entry = some updated) :
  mergeLoLayoutFrame { state with data := updated } = mergeLoLayoutFrame state := by
  have hsize := SortSlice.write_entries_size_of_eq_some _ _ _ _ h
  simp [mergeLoLayoutFrame, hsize]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[dataMemmove_layout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
private lemma dataMemmove_layout (state : MergeState κ ν)
  (updated : SortSlice κ ν) (dst src : Int) (count : Nat)
  (h : state.data.memmove? dst src count = some updated) :
  mergeLoLayoutFrame { state with data := updated } = mergeLoLayoutFrame state := by
  have hsize := SortSlice.memmove_entries_size_of_eq_some _ _ _ _ _ h
  simp [mergeLoLayoutFrame, hsize]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemcpyDataToTemp_layout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
private lemma mergeLoMemcpyDataToTemp_layout
  (site : MergeLoMemcpyCallsite)
  (hDirection : site.backings =
    { destination := .temporary, source := .main })
  (count : Nat) (state state' : MergeState κ ν) (destination : Nat)
  (source : Int)
  (h : mergeLoMemcpyDataToTemp? site hDirection count state destination source =
    some state') :
  mergeLoLayoutFrame state' = mergeLoLayoutFrame state := by
  induction count generalizing state destination source with
  | zero =>
    have := congrArg (Option.map mergeLoLayoutFrame) h
    simpa [mergeLoMemcpyDataToTemp?] using this.symm
  | succ count ih =>
    simp only [mergeLoMemcpyDataToTemp?, bind, Option.bind] at h
    split at h <;> simp_all
    split at h <;> simp_all
    simpa [mergeLoLayoutFrame] using ih _ _ _ h

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoMemcpyTempToData_layout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
private lemma mergeLoMemcpyTempToData_layout
  (site : MergeLoMemcpyCallsite)
  (hDirection : site.backings =
    { destination := .main, source := .temporary })
  (count : Nat) (state state' : MergeState κ ν) (destination : Int)
  (source : Nat)
  (h : mergeLoMemcpyTempToData? site hDirection count state destination source =
    some state') :
  mergeLoLayoutFrame state' = mergeLoLayoutFrame state := by
  induction count generalizing state destination source with
  | zero =>
    have := congrArg (Option.map mergeLoLayoutFrame) h
    simpa [mergeLoMemcpyTempToData?] using this.symm
  | succ count ih =>
    simp only [mergeLoMemcpyTempToData?, bind, Option.bind] at h
    split at h <;> simp_all
    split at h <;> simp_all
    have htail := ih _ _ _ h
    have hsize := SortSlice.write_entries_size_of_eq_some _ _ _ _ ‹_›
    simpa [mergeLoLayoutFrame, hsize] using htail

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoInitialDataToTemp_layout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
private lemma mergeLoInitialDataToTemp_layout
  (count : Nat) (state state' : MergeState κ ν) (destination : Nat)
  (source : Int)
  (h : mergeLoMemcpyDataToTemp? .initialDataToTemp rfl count state
    destination source = some state') :
  mergeLoLayoutFrame state' = mergeLoLayoutFrame state :=
  mergeLoMemcpyDataToTemp_layout .initialDataToTemp rfl count state state'
    destination source h

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoGallopTempToData_layout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
private lemma mergeLoGallopTempToData_layout
  (count : Nat) (state state' : MergeState κ ν) (destination : Int)
  (source : Nat)
  (h : mergeLoMemcpyTempToData? .gallopTempToData rfl count state
    destination source = some state') :
  mergeLoLayoutFrame state' = mergeLoLayoutFrame state :=
  mergeLoMemcpyTempToData_layout .gallopTempToData rfl count state state'
    destination source h

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoFinalTempToData_layout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
private lemma mergeLoFinalTempToData_layout
  (count : Nat) (state state' : MergeState κ ν) (destination : Int)
  (source : Nat)
  (h : mergeLoMemcpyTempToData? .finalTempToData rfl count state
    destination source = some state') :
  mergeLoLayoutFrame state' = mergeLoLayoutFrame state :=
  mergeLoMemcpyTempToData_layout .finalTempToData rfl count state state'
    destination source h

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[copyAIncr_layout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
private lemma copyAIncr_layout
  (machine machine' : MergeLoMachine κ ν)
  (h : mergeLoCopyAIncr? machine = some machine') :
  mergeLoLayoutFrame machine'.state = mergeLoLayoutFrame machine.state := by
  simp only [mergeLoCopyAIncr?, bind, Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  subst machine'
  have hsize := SortSlice.write_entries_size_of_eq_some _ _ _ _ ‹_›
  simp [mergeLoLayoutFrame, hsize]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[copyBIncr_layout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
private lemma copyBIncr_layout
  (machine machine' : MergeLoMachine κ ν)
  (h : mergeLoCopyBIncr? machine = some machine') :
  mergeLoLayoutFrame machine'.state = mergeLoLayoutFrame machine.state := by
  simp only [mergeLoCopyBIncr?, bind, Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  subst machine'
  have hsize := SortSlice.write_entries_size_of_eq_some _ _ _ _ ‹_›
  simp [mergeLoLayoutFrame, hsize]
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoSucceed_layout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
private lemma mergeLoSucceed_layout
  (machine : MergeLoMachine κ ν) (result : MergeLoResult κ ν)
  (h : mergeLoSucceed? machine = some result) :
  mergeLoLayoutFrame result.state = mergeLoLayoutFrame machine.state := by
  simp only [mergeLoSucceed?, bind, Option.bind] at h
  split at h <;> simp_all
  subst result
  apply mergeLoMemcpyTempToData_layout
  assumption

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoCopyB_layout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
private lemma mergeLoCopyB_layout
  (machine : MergeLoMachine κ ν) (result : MergeLoResult κ ν)
  (h : mergeLoCopyB? machine = some result) :
  mergeLoLayoutFrame result.state = mergeLoLayoutFrame machine.state := by
  simp only [mergeLoCopyB?, bind, Option.bind] at h
  split at h
  · split at h <;> simp_all
    split at h <;> simp_all
    split at h <;> simp_all
    subst result
    have hmove := SortSlice.memmove_entries_size_of_eq_some _ _ _ _ _ ‹_›
    have hwrite := SortSlice.write_entries_size_of_eq_some _ _ _ _ ‹_›
    have hsize := hwrite.trans hmove
    simp [mergeLoSuccess, mergeLoLayoutFrame, hsize]
  · simp at h
attribute [aesop safe forward] copyAIncr_layout copyBIncr_layout mergeLoSucceed_layout
  mergeLoCopyB_layout

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[layoutEqTrans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
private lemma layoutEqTrans (first second third : MergeLoLayoutFrame)
  (h₁ : first = second) (h₂ : second = third) : first = third :=
  h₁.trans h₂

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoGallopFuelFailure_layout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
private lemma mergeLoGallopFuelFailure_layout
  (machine : MergeLoMachine κ ν) (result : MergeLoResult κ ν)
  (h : mergeLoGallopFuelFailure machine = some result) :
  mergeLoLayoutFrame result.state = mergeLoLayoutFrame machine.state := by
  simp [mergeLoGallopFuelFailure, mergeLoOutOfFuel] at h
  subst result
  rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeGetmem_layout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
private lemma mergeGetmem_layout (state : MergeState κ ν) (need : PySSize) :
  mergeLoLayoutFrame (mergeGetmem state need).state = mergeLoLayoutFrame state := by
  simp only [mergeGetmem]
  split
  · rfl
  · split <;> simp only
    all_goals simp only [mergeFreemem]
    all_goals split <;> rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoFailure_layout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
private lemma mergeLoFailure_layout (state : MergeState κ ν)
  (result : MergeLoResult κ ν) (h : mergeLoFailure state = result) :
  mergeLoLayoutFrame result.state = mergeLoLayoutFrame state := by
  subst result
  rfl
set_option linter.flexible false in
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoGallopRound_layout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
private lemma mergeLoGallopRound_layout
  (machine : MergeLoMachine κ ν)
  (next : MergeLoMachine κ ν → Nat → Nat → Option (MergeLoResult κ ν))
  (hnext : ∀ machine' aCount bCount result,
    next machine' aCount bCount = some result →
      mergeLoLayoutFrame result.state = mergeLoLayoutFrame machine'.state)
  (result : MergeLoResult κ ν)
  (h : mergeLoGallopRound? machine next = some result) :
  mergeLoLayoutFrame result.state = mergeLoLayoutFrame machine.state := by
  simp only [mergeLoGallopRound?, bind, Option.bind, mergeLoBindOptionAcross] at h
  split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try aesop (config := {
    enableSimp := false, maxRuleApplications := 500, warnOnNonterminal := false })
  all_goals
    obtain ⟨_, _, hresult⟩ := h
    split at hresult
    · have hr := mergeLoCopyB_layout _ _ hresult
      aesop (config := { enableSimp := false, maxRuleApplications := 500 })
    · have hr := hnext _ _ _ _ hresult
      aesop (config := { enableSimp := false, maxRuleApplications := 500 })
set_option linter.flexible false in
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeLoLoop_layout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
private lemma mergeLoLoop_layout
  (fuel : Nat) (machine : MergeLoMachine κ ν) (phase : MergeLoPhase)
  (result : MergeLoResult κ ν)
  (h : mergeLoLoop? fuel machine phase = some result) :
  mergeLoLayoutFrame result.state = mergeLoLayoutFrame machine.state := by
  induction fuel generalizing machine phase result with
  | zero =>
    simp only [mergeLoLoop?] at h
    have := congrArg (fun r => mergeLoLayoutFrame r.state) (Option.some.inj h)
    simpa [mergeLoOutOfFuel] using this.symm
  | succ fuel ih =>
    cases phase with
    | ordinary aCount bCount =>
      simp only [mergeLoLoop?, bind, Option.bind] at h
      split at h <;> try simp at h
      all_goals try split at h <;> try simp at h
      all_goals try split at h <;> try simp at h
      all_goals try split at h <;> try simp at h
      all_goals try split at h <;> try simp at h
      all_goals try split at h <;> try simp at h
      all_goals try split at h <;> try simp at h
      all_goals try aesop (config := {
        enableSimp := false, maxRuleApplications := 500,
        warnOnNonterminal := false })
      all_goals exact (ih _ _ _ h).trans fwd
    | galloping =>
      let next : MergeLoMachine κ ν → Nat → Nat → Option (MergeLoResult κ ν) :=
        fun machine' aCount bCount =>
        if MIN_GALLOP.toNat ≤ aCount ∨ MIN_GALLOP.toNat ≤ bCount then
          mergeLoLoop? fuel machine' .galloping
        else
          let minGallop := machine'.minGallop + 1
          let state := { machine'.state with min_gallop := minGallop }
          mergeLoLoop? fuel
            { machine' with state := state, minGallop := minGallop }
            (.ordinary 0 0)
      have hround : mergeLoGallopRound? machine next = some result := by
        simpa only [mergeLoLoop?] using h
      apply mergeLoGallopRound_layout machine next _ result hround
      · intro machine' aCount bCount result' hresult
        dsimp only [next] at hresult
        split at hresult
        · exact ih machine' .galloping result' hresult
        · have hframe := ih _ (.ordinary 0 0) result' hresult
          simpa [mergeLoLayoutFrame] using hframe
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

/--
[mergeLo_layout_frame_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLo_layout_frame_of_eq_some
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {ssa ssb : Int}
  {na nb : Nat}
  {result : MergeLoResult κ ν}
-- given
  (h : mergeLo? state ssa ssb na nb = some result) :
-- imply
  result.state.listlen = state.listlen ∧ result.state.basekeys = state.basekeys ∧ result.state.data.entries.size = state.data.entries.size ∧ result.state.pending = state.pending := by
-- proof
  have hframe :
    mergeLoLayoutFrame result.state = mergeLoLayoutFrame state := by
    simp only [mergeLo?, bind, Option.bind] at h
    split at h <;> try simp at h
    all_goals try split at h <;> try simp at h
    all_goals try split at h <;> try simp at h
    all_goals try split at h <;> try simp at h
    all_goals try split at h <;> try simp at h
    all_goals try split at h <;> try simp at h
    all_goals aesop (config := { enableSimp := false, warnOnNonterminal := false })
    all_goals first
      | simpa [mergeLoFailure] using
        (mergeGetmem_layout state (BitVec.ofNat 64 na))
      | apply Eq.trans ?_ (mergeGetmem_layout state (BitVec.ofNat 64 na))
        assumption
  exact
    ⟨congrArg MergeLoLayoutFrame.listlen hframe,
      congrArg MergeLoLayoutFrame.basekeys hframe,
      congrArg MergeLoLayoutFrame.dataSize hframe,
      congrArg MergeLoLayoutFrame.pending hframe⟩

end CPythonListsort

namespace CPythonListsort

/--
[mergeLo_pending_eq_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLo_pending_eq_of_eq_some
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {ssa ssb : Int}
  {na nb : Nat}
  {result : MergeLoResult κ ν}
-- given
  (h : mergeLo? state ssa ssb na nb = some result) :
-- imply
  result.state.pending = state.pending :=
-- proof
  (mergeLo_layout_frame_of_eq_some state ssa ssb na nb result h).2.2.2

end CPythonListsort

namespace CPythonListsort

/--
[mergeLo_straight_stability_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLo_straight_stability_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (mergeLo? mergeLoStabilityRegressionState 0 2 2 3).map (fun result => (result.returnCode, result.fuelExhausted, result.state.data.entries.toList)) = some (0, false, [{ key := 2, value := some 20 }, { key := 3, value := some 30 }, { key := 3, value := some 32 }, { key := 3, value := some 33 }, { key := 4, value := some 40 }]) := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[mergeLo_gallop_stability_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLo_gallop_stability_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (mergeLo? mergeLoGallopStabilityRegressionState 0 3 3 3).map (fun result => (result.returnCode, result.fuelExhausted, result.state.min_gallop, result.state.data.entries.toList)) = some (0, false, 1, [{ key := 1, value := some 10 }, { key := 2, value := some 20 }, { key := 3, value := some 30 }, { key := 3, value := some 31 }, { key := 4, value := some 40 }, { key := 5, value := some 50 }]) := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[mergeLo_inconsistentComparator_naZero_succeed_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
lemma mergeLo_inconsistentComparator_naZero_succeed_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  mergeLoNaZeroHedgeRegressionState.key_compare 1 1 = true ∧ ((mergeLoTempRun? mergeLoNaZeroHedgeRegressionState.a 0 2).bind (fun activeA => gallopRight? mergeLoNaZeroHedgeRegressionState activeA 0 0 2 0)) = some { index := 2, fuelExhausted := false } ∧ ((mergeLoTempRun? mergeLoNaZeroHedgeStrictControlState.a 0 2).bind (fun activeA => gallopRight? mergeLoNaZeroHedgeStrictControlState activeA 0 0 2 0)) = some { index := 0, fuelExhausted := false } ∧ (mergeLoGallopRound? mergeLoNaZeroHedgeRegressionMachine (fun _ _ _ => none)).map (fun result => (result.returnCode, result.fuelExhausted, result.state.data.entries.toList)) = some (0, false, [{ key := 1, value := some 10 }, { key := 2, value := some 20 }, { key := 0, value := some 0 }]) ∧ (mergeLoGallopRound? mergeLoNaZeroHedgeStrictControlMachine (fun _ _ _ => none)).map (fun result => (result.returnCode, result.fuelExhausted, result.state.data.entries.toList)) = some (0, false, [{ key := 0, value := some 0 }, { key := 1, value := some 10 }, { key := 2, value := some 20 }]) := by
-- proof
  decide

end CPythonListsort

/--
[mergeLo_memcpyCallsite_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean)
-/
@[path]
private lemma mergeLo_memcpyCallsite_distinct_eq
  {κ : Type u}
  {ν : Type v}
  {site : MergeLoMemcpyCallsite} :
-- imply
  site.backings.Distinct := by
-- proof
  apply CPythonListsort.mergeLo_memcpyCallsite_distinct site


-- created on 2026-10-23

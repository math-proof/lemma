import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.CPythonListsort.Code.Transcription.MergeHi.Part6
open CPythonListsort


namespace CPythonListsort

/--
[mergeHiTempRead_ofNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiTempRead_ofNat
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {index : Nat} :
-- imply
  mergeHiTempRead? storage (Int.ofNat index) = storage.cells[index]?.bind id := by
-- proof
  cases hcell : storage.cells[index]? with
  | none => simp [mergeHiTempRead?, hcell]
  | some cell => cases cell <;> simp [mergeHiTempRead?, hcell]

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiTempWrite_read_eq_some_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiTempWrite_read_eq_some_of_eq_some
  {κ : Type u}
  {ν : Type v}
  {storage updated : TempStorage κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν}
-- given
  (hwrite : mergeHiTempWrite? storage index entry = some updated) :
-- imply
  mergeHiTempRead? updated index = some entry := by
-- proof
  unfold mergeHiTempWrite? at hwrite
  split at hwrite
  · rename_i hnonnegative
    dsimp only at hwrite
    split at hwrite
    · rename_i hinBounds
      injection hwrite with hwrite
      subst updated
      simp [mergeHiTempRead?, hnonnegative, hinBounds]
    · simp at hwrite
  · simp at hwrite

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiTempWrite_read_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiTempWrite_read_of_ne
  {κ : Type u}
  {ν : Type v}
  {storage updated : TempStorage κ ν}
  {written index : Int}
  {entry : SortSliceEntry κ ν}
-- given
  (hwrite : mergeHiTempWrite? storage written entry = some updated)
  (hne : index ≠ written) :
-- imply
  mergeHiTempRead? updated index = mergeHiTempRead? storage index := by
-- proof
  unfold mergeHiTempWrite? at hwrite
  split at hwrite
  · rename_i hwritten
    dsimp only at hwrite
    split at hwrite
    · rename_i hinBounds
      injection hwrite with hwrite
      subst updated
      by_cases hindex : 0 ≤ index
      · have hnatne : written.toNat ≠ index.toNat := by
        intro heq
        apply hne
        have hwrittenCast := Int.toNat_of_nonneg hwritten
        have hindexCast := Int.toNat_of_nonneg hindex
        omega
        simp [mergeHiTempRead?, hindex, Array.getElem?_set_ne _ hnatne]
      · simp [mergeHiTempRead?, hindex]
    · simp at hwrite
  · simp at hwrite

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiCopyDataToTemp_read_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiCopyDataToTemp_read_eq_some
  {κ : Type u}
  {ν : Type v}
  {state state' : MergeState κ ν}
  {dst src : Int}
-- given
  (hcopy : mergeHiCopyDataToTemp? state dst src = some state') :
-- imply
  ∃ entry, state.data.read? src = some entry ∧ mergeHiTempRead? state'.a dst = some entry := by
-- proof
  obtain ⟨entry, hread, htail⟩ := Option.bind_eq_some_iff.mp hcopy
  obtain ⟨storage, hwrite, hfinal⟩ := Option.bind_eq_some_iff.mp htail
  injection hfinal with hfinal
  subst state'
  exact ⟨entry, hread,
    mergeHiTempWrite_read_eq_some_of_eq_some state.a storage dst entry hwrite⟩

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiCopyDataToTemp_read_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiCopyDataToTemp_read_of_ne
  {κ : Type u}
  {ν : Type v}
  {state state' : MergeState κ ν}
  {dst src index : Int}
-- given
  (hcopy : mergeHiCopyDataToTemp? state dst src = some state')
  (hne : index ≠ dst) :
-- imply
  mergeHiTempRead? state'.a index = mergeHiTempRead? state.a index := by
-- proof
  obtain ⟨entry, _hread, htail⟩ := Option.bind_eq_some_iff.mp hcopy
  obtain ⟨storage, hwrite, hfinal⟩ := Option.bind_eq_some_iff.mp htail
  injection hfinal with hfinal
  subst state'
  exact mergeHiTempWrite_read_of_ne state.a storage dst index _ hwrite hne

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiMemcpyDataToTemp_read_before](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiMemcpyDataToTemp_read_before
  {κ : Type u}
  {ν : Type v}
  {site : MergeHiMemcpyCallsite}
  {count : Nat}
  {state state' : MergeState κ ν}
  {dst src index : Int}
-- given
  (hDirection : site.backings = { destination := .temporary, source := .main })
  (hcopy : mergeHiMemcpyDataToTemp? site hDirection count state dst src = some state')
  (hindex : index < dst) :
-- imply
  mergeHiTempRead? state'.a index = mergeHiTempRead? state.a index := by
-- proof
  induction count generalizing state dst src with
  | zero =>
    simp only [mergeHiMemcpyDataToTemp?] at hcopy
    injection hcopy with hcopy
    subst state'
    rfl
  | succ count ih =>
    rw [mergeHiMemcpyDataToTemp?] at hcopy
    obtain ⟨afterHead, hhead, hcopy⟩ := Option.bind_eq_some_iff.mp hcopy
    have htail := ih afterHead (dst + 1) (src + 1) hcopy (by omega)
    exact htail.trans
      (mergeHiCopyDataToTemp_read_of_ne state afterHead dst src index hhead
        (by omega))

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiMemcpyDataToTemp_initialized_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiMemcpyDataToTemp_initialized_of_eq_some
  {κ : Type u}
  {ν : Type v}
  {site : MergeHiMemcpyCallsite}
  {count : Nat}
  {state state' : MergeState κ ν}
  {dst src : Int}
-- given
  (hDirection : site.backings = { destination := .temporary, source := .main })
  (hcopy : mergeHiMemcpyDataToTemp? site hDirection count state dst src = some state') :
-- imply
  MergeHiTempRangeInitialized state'.a dst count := by
-- proof
  induction count generalizing state dst src with
  | zero =>
    unfold MergeHiTempRangeInitialized
    intro i hi
    omega
  | succ count ih =>
    rw [mergeHiMemcpyDataToTemp?] at hcopy
    obtain ⟨afterHead, hhead, hcopy⟩ := Option.bind_eq_some_iff.mp hcopy
    intro i hi
    cases i with
    | zero =>
      rcases mergeHiCopyDataToTemp_read_eq_some state afterHead dst src hhead with
        ⟨entry, _hsource, hread⟩
      refine ⟨entry, ?_⟩
      have hpreserved := mergeHiMemcpyDataToTemp_read_before site hDirection
        count afterHead state' (dst + 1) (src + 1) dst hcopy (by omega)
      simpa using hpreserved.trans hread
    | succ i =>
      rcases ih afterHead (dst + 1) (src + 1) hcopy i (by omega) with
        ⟨entry, hread⟩
      exact ⟨entry, by
        have hindex :
          dst + Int.ofNat (Nat.succ i) =
            (dst + 1) + Int.ofNat i := by
          simp [Int.ofNat_eq_natCast]
          omega
        rw [hindex]
        exact hread⟩

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiInitialDataToTemp_prefixInitialized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiInitialDataToTemp_prefixInitialized
  {κ : Type u}
  {ν : Type v}
  {count : Nat}
  {state state' : MergeState κ ν}
  {src : Int}
-- given
  (hcopy : mergeHiMemcpyDataToTemp? .initialDataToTemp rfl count state 0 src = some state') :
-- imply
  MergeHiTempPrefixInitialized state'.a count := by
-- proof
  simpa [MergeHiTempPrefixInitialized] using
    (mergeHiMemcpyDataToTemp_initialized_of_eq_some .initialDataToTemp rfl count
      state state' 0 src hcopy)

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiInitializedTempPrefixLoop_exists_of_initialized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiInitializedTempPrefixLoop_exists_of_initialized
  {κ : Type u}
  {ν : Type v}
  {count : Nat}
  {storage : TempStorage κ ν}
  {source : Nat}
  {initial : Array (SortSliceEntry κ ν)}
-- given
  (hInitialized : ∀ i, i < count → ∃ entry, mergeHiTempRead? storage (Int.ofNat (source + i)) = some entry) :
-- imply
  ∃ result, mergeHiInitializedTempPrefixLoop? count storage source initial = some result := by
-- proof
  induction count generalizing source initial with
  | zero =>
    exact ⟨initial, rfl⟩
  | succ count ih =>
    obtain ⟨entry, hentry⟩ := hInitialized 0 (Nat.zero_lt_succ count)
    have hhead :
      mergeHiTempRead? storage (Int.ofNat source) = some entry := by
      simpa using hentry
    rcases ih (source + 1) (initial.push entry) (fun i hi => by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hInitialized (i + 1) (by omega)) with ⟨result, hresult⟩
    exact ⟨result, by
      simp only [mergeHiInitializedTempPrefixLoop?]
      rw [hhead]
      exact hresult⟩

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiInitializedTempPrefix_exists_of_initialized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiInitializedTempPrefix_exists_of_initialized
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {count : Nat}
-- given
  (hInitialized : MergeHiTempPrefixInitialized storage count) :
-- imply
  ∃ slice, initializedTempPrefix? storage count = some slice := by
-- proof
  rcases mergeHiInitializedTempPrefixLoop_exists_of_initialized count storage
    0 #[] (by
      simpa [MergeHiTempPrefixInitialized, MergeHiTempRangeInitialized] using
        hInitialized) with
    ⟨entries, hentries⟩
  exact ⟨{ entries := entries }, by
    simp [initializedTempPrefix?, hentries]⟩

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiInitialDataToTemp_initializedTempPrefix_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiInitialDataToTemp_initializedTempPrefix_exists
  {κ : Type u}
  {ν : Type v}
  {count : Nat}
  {state state' : MergeState κ ν}
  {src : Int}
-- given
  (hcopy : mergeHiMemcpyDataToTemp? .initialDataToTemp rfl count state 0 src = some state') :
-- imply
  ∃ slice, initializedTempPrefix? state'.a count = some slice :=
-- proof
  mergeHiInitializedTempPrefix_exists_of_initialized state'.a count
    (mergeHiInitialDataToTemp_prefixInitialized count state state' src hcopy)

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiInitializedTempPrefixLoop_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiInitializedTempPrefixLoop_spec
  {κ : Type u}
  {ν : Type v}
  {count : Nat}
  {storage : TempStorage κ ν}
  {source : Nat}
  {initial result : Array (SortSliceEntry κ ν)}
-- given
  (hresult : mergeHiInitializedTempPrefixLoop? count storage source initial = some result) :
-- imply
  result.size = initial.size + count ∧ (∀ i < initial.size, result[i]? = initial[i]?) ∧ ∀ i < count, result[initial.size + i]? = storage.cells[source + i]?.bind id := by
-- proof
  induction count generalizing source initial with
  | zero =>
    simp only [mergeHiInitializedTempPrefixLoop?] at hresult
    injection hresult with hresult
    subst result
    simp
  | succ count ih =>
    cases hcell : storage.cells[source]? with
    | none =>
      simp [mergeHiInitializedTempPrefixLoop?, mergeHiTempRead?, hcell] at hresult
    | some cell =>
      cases cell with
      | none =>
        simp [mergeHiInitializedTempPrefixLoop?, mergeHiTempRead?, hcell] at hresult
      | some entry =>
        have hnext :
          mergeHiInitializedTempPrefixLoop? count storage (source + 1)
            (initial.push entry) = some result := by
          simpa [mergeHiInitializedTempPrefixLoop?, mergeHiTempRead?, hcell] using
            hresult
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
[initializedTempPrefix_cells_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma initializedTempPrefix_cells_of_eq_some
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {count : Nat}
  {slice : SortSlice κ ν}
-- given
  (hresult : initializedTempPrefix? storage count = some slice) :
-- imply
  slice.entries.size = count ∧ ∀ i < count, storage.cells[i]?.bind id = slice.entries[i]? := by
-- proof
  unfold initializedTempPrefix? at hresult
  cases hentries : mergeHiInitializedTempPrefixLoop? count storage 0 #[] with
  | none => simp [hentries] at hresult
  | some entries =>
    have hmaterialized :
      (some ({ entries := entries } : SortSlice κ ν)) = some slice := by
      simpa [hentries] using hresult
    injection hmaterialized with hmaterialized
    subst slice
    rcases mergeHiInitializedTempPrefixLoop_spec count storage 0 #[] entries hentries with
      ⟨hsize, _hprefix, hrange⟩
    exact ⟨by simpa using hsize, fun i hi => by
      simpa using (hrange i hi).symm⟩

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiInitializedTempPrefix_initialized_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiInitializedTempPrefix_initialized_of_eq_some
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {count : Nat}
  {slice : SortSlice κ ν}
-- given
  (hresult : initializedTempPrefix? storage count = some slice) :
-- imply
  MergeHiTempPrefixInitialized storage count := by
-- proof
  rcases initializedTempPrefix_cells_of_eq_some storage count slice hresult with
    ⟨hsize, hcells⟩
  intro i hi
  have hiSize : i < slice.entries.size := by omega
  have hslice := Array.getElem?_eq_getElem hiSize
  have hbind :
    storage.cells[i]?.bind id = some slice.entries[i] := by
    rw [hcells i hi, hslice]
  rw [Option.bind_eq_some_iff] at hbind
  obtain ⟨cell, hcell, hcellEntry⟩ := hbind
  have hcellEntry' : cell = some slice.entries[i] := by
    simpa using hcellEntry
  subst cell
  exact ⟨slice.entries[i], by
    simp [mergeHiTempRead?, hcell]⟩

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiInitializedTempPrefix_exists_iff_initialized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiInitializedTempPrefix_exists_iff_initialized
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {count : Nat} :
-- imply
  (∃ slice, initializedTempPrefix? storage count = some slice) ↔ MergeHiTempPrefixInitialized storage count := by
-- proof
  constructor
  · rintro ⟨slice, hslice⟩
    exact mergeHiInitializedTempPrefix_initialized_of_eq_some storage count slice
      hslice
  · exact mergeHiInitializedTempPrefix_exists_of_initialized storage count

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiCopyDataDecr_equation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiCopyDataDecr_equation
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {dst src : Int} :
-- imply
  mergeHiCopyDataDecr? state dst src = (do let copied ← state.data.copyDecr? dst src pure { state := { state with data := copied.slice } dst := copied.dst src := copied.src }) := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiCopyTempDecr_equation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiCopyTempDecr_equation
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {dst src : Int} :
-- imply
  mergeHiCopyTempDecr? state dst src = (do let state ← mergeHiCopyTempToData? state dst src pure { state := state, dst := dst - 1, src := src - 1 }) := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiCopyA_memmove_equation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiCopyA_memmove_equation
  {κ : Type u}
  {ν : Type v}
  {cursor : MergeHiCursor κ ν} :
-- imply
  mergeHiCopyA? cursor = (do if cursor.nb = 1 ∧ 0 < cursor.na then let offset := 1 - Int.ofNat cursor.na let data ← mergeDataMemmove? .hiCopyATail cursor.state.data (cursor.dest + offset) (cursor.ssa + offset) cursor.na let state := { cursor.state with data := data } let state ← mergeHiCopyTempToData? state (cursor.dest - Int.ofNat cursor.na) cursor.ssb pure { state := state, returnCode := 0, fuelExhausted := false } else none) := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiGallopB_equation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiGallopB_equation
  {κ : Type u}
  {ν : Type v}
  {afterB : MergeHiCursor κ ν}
  {aCount : Nat}
  {next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)} :
-- imply
  mergeHiGallopB? afterB aCount next = (do let left ← afterB.state.data.read? afterB.ssa let temp ← initializedTempPrefix? afterB.state.a afterB.nb mergeHiBindOptionAcross (gallopLeft? afterB.state temp 0 left.key afterB.nb (afterB.nb - 1)) fun gallopB => if gallopB.fuelExhausted then some (mergeHiFuelExhausted afterB) else do let bCount := afterB.nb - gallopB.index let movedB ← if bCount = 0 then some afterB else do let dest := afterB.dest - Int.ofNat bCount let ssb := afterB.ssb - Int.ofNat bCount let state ← mergeHiMemcpyTempToData? .gallopTempToData rfl bCount afterB.state (dest + 1) (ssb + 1) some { afterB with state := state dest := dest ssb := ssb nb := afterB.nb - bCount } if movedB.nb = 0 ∨ movedB.nb = 1 then next movedB else let copiedA ← mergeHiCopyDataDecr? movedB.state movedB.dest movedB.ssa let afterA : MergeHiCursor κ ν := { movedB with state := copiedA.state dest := copiedA.dst ssa := copiedA.src na := movedB.na - 1 } if afterA.na = 0 then next afterA else if mergeHiCountAtLeast aCount MIN_GALLOP || mergeHiCountAtLeast bCount MIN_GALLOP then next { afterA with phase := .galloping aCount bCount } else let minGallop := afterB.minGallop + 1 let state := { afterA.state with min_gallop := minGallop } next { afterA with state := state minGallop := minGallop phase := .straight 0 0 }) := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiGallopRound_equation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiGallopRound_equation
  {κ : Type u}
  {ν : Type v}
  {cursor : MergeHiCursor κ ν}
  {next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)} :
-- imply
  mergeHiGallopRound? cursor next = (do let minGallop := mergeHiDecreaseMinGallop cursor.minGallop let state := { cursor.state with min_gallop := minGallop } let right ← mergeHiTempRead? state.a cursor.ssb mergeHiBindOptionAcross (gallopRight? state state.data cursor.basea right.key cursor.na (cursor.na - 1)) fun gallopA => if gallopA.fuelExhausted then some (mergeHiFuelExhausted { cursor with state := state }) else do let aCount := cursor.na - gallopA.index let movedA ← if aCount = 0 then some { cursor with state := state, minGallop := minGallop } else do let dest := cursor.dest - Int.ofNat aCount let ssa := cursor.ssa - Int.ofNat aCount let data ← mergeDataMemmove? .hiGallopA state.data (dest + 1) (ssa + 1) aCount some { cursor with state := { state with data := data } dest := dest ssa := ssa na := cursor.na - aCount minGallop := minGallop } if movedA.na = 0 then next movedA else let copiedB ← mergeHiCopyTempDecr? movedA.state movedA.dest movedA.ssb let afterB : MergeHiCursor κ ν := { movedA with state := copiedB.state dest := copiedB.dst ssb := copiedB.src nb := movedA.nb - 1 } if afterB.nb = 1 then next afterB else mergeHiGallopB? afterB aCount next) := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiLoop_straight_copyA_equation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiLoop_straight_copyA_equation
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {cursor : MergeHiCursor κ ν}
  {aCount bCount : Nat}
  {right left : SortSliceEntry κ ν}
-- given
  (hactive : ¬ (cursor.na = 0 ∨ cursor.nb = 0))
  (hmoreB : cursor.nb ≠ 1)
  (hright : mergeHiTempRead? cursor.state.a cursor.ssb = some right)
  (hleft : cursor.state.data.read? cursor.ssa = some left)
  (hcompare : cursor.state.key_compare right.key left.key = true) :
-- imply
  mergeHiLoop? (fuel + 1) { cursor with phase := .straight aCount bCount } = (do let copied ← mergeHiCopyDataDecr? cursor.state cursor.dest cursor.ssa let aCount := aCount + 1 let next : MergeHiCursor κ ν := { cursor with state := copied.state dest := copied.dst ssa := copied.src na := cursor.na - 1 phase := if mergeHiCountAtLeast aCount cursor.minGallop then .galloping aCount 0 else .straight aCount 0 minGallop := if mergeHiCountAtLeast aCount cursor.minGallop then cursor.minGallop + 1 else cursor.minGallop } mergeHiLoop? fuel next) := by
-- proof
  rw [mergeHiLoop?]
  simp [hactive, hmoreB, hright, hleft, iflt, hcompare]

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiLoop_straight_copyB_equation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiLoop_straight_copyB_equation
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {cursor : MergeHiCursor κ ν}
  {aCount bCount : Nat}
  {right left : SortSliceEntry κ ν}
-- given
  (hactive : ¬ (cursor.na = 0 ∨ cursor.nb = 0))
  (hmoreB : cursor.nb ≠ 1)
  (hright : mergeHiTempRead? cursor.state.a cursor.ssb = some right)
  (hleft : cursor.state.data.read? cursor.ssa = some left)
  (hcompare : cursor.state.key_compare right.key left.key = false) :
-- imply
  mergeHiLoop? (fuel + 1) { cursor with phase := .straight aCount bCount } = (do let copied ← mergeHiCopyTempDecr? cursor.state cursor.dest cursor.ssb let bCount := bCount + 1 let next : MergeHiCursor κ ν := { cursor with state := copied.state dest := copied.dst ssb := copied.src nb := cursor.nb - 1 phase := if mergeHiCountAtLeast bCount cursor.minGallop then .galloping 0 bCount else .straight 0 bCount minGallop := if mergeHiCountAtLeast bCount cursor.minGallop then cursor.minGallop + 1 else cursor.minGallop } mergeHiLoop? fuel next) := by
-- proof
  rw [mergeHiLoop?]
  simp [hactive, hmoreB, hright, hleft, iflt, hcompare]

end CPythonListsort

namespace CPythonListsort

/--
[mergeHiLoop_straight_equal_keys_equation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHiLoop_straight_equal_keys_equation
  {κ : Type u}
  {ν : Type v}
  {fuel : Nat}
  {cursor : MergeHiCursor κ ν}
  {aCount bCount : Nat}
  {right left : SortSliceEntry κ ν}
-- given
  (hactive : ¬ (cursor.na = 0 ∨ cursor.nb = 0))
  (hmoreB : cursor.nb ≠ 1)
  (hright : mergeHiTempRead? cursor.state.a cursor.ssb = some right)
  (hleft : cursor.state.data.read? cursor.ssa = some left)
  (hkeys : right.key = left.key)
  (hirrefl : cursor.state.key_compare left.key left.key = false) :
-- imply
  mergeHiLoop? (fuel + 1) { cursor with phase := .straight aCount bCount } = (do let copied ← mergeHiCopyTempDecr? cursor.state cursor.dest cursor.ssb let bCount := bCount + 1 let next : MergeHiCursor κ ν := { cursor with state := copied.state dest := copied.dst ssb := copied.src nb := cursor.nb - 1 phase := if mergeHiCountAtLeast bCount cursor.minGallop then .galloping 0 bCount else .straight 0 bCount minGallop := if mergeHiCountAtLeast bCount cursor.minGallop then cursor.minGallop + 1 else cursor.minGallop } mergeHiLoop? fuel next) := by
-- proof
  apply mergeHiLoop_straight_copyB_equation fuel cursor aCount bCount
    right left hactive hmoreB hright hleft
  simpa [hkeys] using hirrefl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[copyDataToTemp_layoutFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
private lemma copyDataToTemp_layoutFrame
  (state state' : MergeState κ ν) (dst src : Int)
  (h : mergeHiCopyDataToTemp? state dst src = some state') :
  mergeHiLayoutFrame state' = mergeHiLayoutFrame state := by
  simp only [mergeHiCopyDataToTemp?, bind, Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  subst state'
  rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemcpyDataToTemp_layoutFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
private lemma mergeHiMemcpyDataToTemp_layoutFrame
  (site : MergeHiMemcpyCallsite)
  (hDirection : site.backings =
    { destination := .temporary, source := .main })
  (count : Nat) (state state' : MergeState κ ν) (dst src : Int)
  (h : mergeHiMemcpyDataToTemp? site hDirection count state dst src =
    some state') :
  mergeHiLayoutFrame state' = mergeHiLayoutFrame state := by
  induction count generalizing state dst src with
  | zero =>
    have := congrArg (Option.map mergeHiLayoutFrame) h
    simpa [mergeHiMemcpyDataToTemp?] using this.symm
  | succ count ih =>
    simp only [mergeHiMemcpyDataToTemp?, bind, Option.bind] at h
    split at h
    · simp at h
    · exact (ih _ _ _ h).trans (copyDataToTemp_layoutFrame _ _ _ _ ‹_›)

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[copyTempToData_layoutFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
private lemma copyTempToData_layoutFrame
  (state state' : MergeState κ ν) (dst src : Int)
  (h : mergeHiCopyTempToData? state dst src = some state') :
  mergeHiLayoutFrame state' = mergeHiLayoutFrame state := by
  simp only [mergeHiCopyTempToData?, bind, Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  subst state'
  have hsize := SortSlice.write_entries_size_of_eq_some _ _ _ _ ‹_›
  simp [mergeHiLayoutFrame, hsize]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiMemcpyTempToData_layoutFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
private lemma mergeHiMemcpyTempToData_layoutFrame
  (site : MergeHiMemcpyCallsite)
  (hDirection : site.backings =
    { destination := .main, source := .temporary })
  (count : Nat) (state state' : MergeState κ ν) (dst src : Int)
  (h : mergeHiMemcpyTempToData? site hDirection count state dst src =
    some state') :
  mergeHiLayoutFrame state' = mergeHiLayoutFrame state := by
  induction count generalizing state dst src with
  | zero =>
    have := congrArg (Option.map mergeHiLayoutFrame) h
    simpa [mergeHiMemcpyTempToData?] using this.symm
  | succ count ih =>
    simp only [mergeHiMemcpyTempToData?, bind, Option.bind] at h
    split at h
    · simp at h
    · exact (ih _ _ _ h).trans (copyTempToData_layoutFrame _ _ _ _ ‹_›)

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiInitialDataToTemp_layoutFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
private lemma mergeHiInitialDataToTemp_layoutFrame
  (count : Nat) (state state' : MergeState κ ν) (dst src : Int)
  (h : mergeHiMemcpyDataToTemp? .initialDataToTemp rfl count state dst src =
    some state') :
  mergeHiLayoutFrame state' = mergeHiLayoutFrame state :=
  mergeHiMemcpyDataToTemp_layoutFrame .initialDataToTemp rfl count state state'
    dst src h

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiGallopTempToData_layoutFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
private lemma mergeHiGallopTempToData_layoutFrame
  (count : Nat) (state state' : MergeState κ ν) (dst src : Int)
  (h : mergeHiMemcpyTempToData? .gallopTempToData rfl count state dst src =
    some state') :
  mergeHiLayoutFrame state' = mergeHiLayoutFrame state :=
  mergeHiMemcpyTempToData_layoutFrame .gallopTempToData rfl count state state'
    dst src h

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiFinalTempToData_layoutFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
private lemma mergeHiFinalTempToData_layoutFrame
  (count : Nat) (state state' : MergeState κ ν) (dst src : Int)
  (h : mergeHiMemcpyTempToData? .finalTempToData rfl count state dst src =
    some state') :
  mergeHiLayoutFrame state' = mergeHiLayoutFrame state :=
  mergeHiMemcpyTempToData_layoutFrame .finalTempToData rfl count state state'
    dst src h

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[copyDataDecr_layoutFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
private lemma copyDataDecr_layoutFrame
  (state : MergeState κ ν) (dst src : Int)
  (result : MergeHiDataCursorResult κ ν)
  (h : mergeHiCopyDataDecr? state dst src = some result) :
  mergeHiLayoutFrame result.state = mergeHiLayoutFrame state := by
  simp only [mergeHiCopyDataDecr?, bind, Option.bind] at h
  split at h <;> simp_all
  subst result
  have hsize := SortSlice.copyDecr_entries_size_of_eq_some _ _ _ _ ‹_›
  simp [mergeHiLayoutFrame, hsize]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[copyTempDecr_layoutFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
private lemma copyTempDecr_layoutFrame
  (state : MergeState κ ν) (dst src : Int)
  (result : MergeHiDataCursorResult κ ν)
  (h : mergeHiCopyTempDecr? state dst src = some result) :
  mergeHiLayoutFrame result.state = mergeHiLayoutFrame state := by
  simp only [mergeHiCopyTempDecr?, bind, Option.bind] at h
  split at h
  · simp at h
  · rename_i state' hcopy
    have hresult :
      { state := state', dst := dst - 1, src := src - 1 } = result := by
      simpa using h
    rw [← hresult]
    exact copyTempToData_layoutFrame _ _ _ _ hcopy
attribute [aesop safe forward] copyDataDecr_layoutFrame copyTempDecr_layoutFrame
  copyTempToData_layoutFrame
attribute [aesop safe forward] SortSlice.memmove_entries_size_of_eq_some

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiSucceed_layoutFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
private lemma mergeHiSucceed_layoutFrame
  (cursor : MergeHiCursor κ ν) (result : MergeHiResult κ ν)
  (h : mergeHiSucceed? cursor = some result) :
  mergeHiLayoutFrame result.state = mergeHiLayoutFrame cursor.state := by
  simp only [mergeHiSucceed?, bind, Option.bind] at h
  split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals aesop (config := { enableSimp := false })

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiCopyA_layoutFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
private lemma mergeHiCopyA_layoutFrame
  (cursor : MergeHiCursor κ ν) (result : MergeHiResult κ ν)
  (h : mergeHiCopyA? cursor = some result) :
  mergeHiLayoutFrame result.state = mergeHiLayoutFrame cursor.state := by
  simp only [mergeHiCopyA?, bind, Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  subst result
  have hmove := SortSlice.memmove_entries_size_of_eq_some _ _ _ _ _ ‹_›
  have hcopy := copyTempToData_layoutFrame _ _ _ _ ‹_›
  simp_all [mergeHiLayoutFrame]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiFuelExhausted_layoutFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
private lemma mergeHiFuelExhausted_layoutFrame
  (cursor : MergeHiCursor κ ν) (result : MergeHiResult κ ν)
  (h : mergeHiFuelExhausted cursor = result) :
  mergeHiLayoutFrame result.state = mergeHiLayoutFrame cursor.state := by
  subst result
  rfl
attribute [aesop safe forward] mergeHiSucceed_layoutFrame mergeHiCopyA_layoutFrame
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiGallopB_layoutFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
private lemma mergeHiGallopB_layoutFrame
  (afterB : MergeHiCursor κ ν) (aCount : Nat)
  (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
  (hnext : ∀ cursor result, next cursor = some result →
    mergeHiLayoutFrame result.state = mergeHiLayoutFrame cursor.state)
  (result : MergeHiResult κ ν)
  (h : mergeHiGallopB? afterB aCount next = some result) :
  mergeHiLayoutFrame result.state = mergeHiLayoutFrame afterB.state := by
  simp only [mergeHiGallopB?, bind, Option.bind, mergeHiBindOptionAcross] at h
  split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try simp only [Option.some.injEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals aesop (config := {
    enableSimp := false, maxRuleApplications := 500, warnOnNonterminal := false })
  all_goals
    have hr := hnext _ _ h
    simp_all only [mergeHiLayoutFrame]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiGallopRound_layoutFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
private lemma mergeHiGallopRound_layoutFrame
  (cursor : MergeHiCursor κ ν)
  (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
  (hnext : ∀ cursor' result, next cursor' = some result →
    mergeHiLayoutFrame result.state = mergeHiLayoutFrame cursor'.state)
  (result : MergeHiResult κ ν)
  (h : mergeHiGallopRound? cursor next = some result) :
  mergeHiLayoutFrame result.state = mergeHiLayoutFrame cursor.state := by
  simp only [mergeHiGallopRound?, bind, Option.bind, mergeHiBindOptionAcross] at h
  split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try simp only [Option.some.injEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try aesop (config := {
    enableSimp := false, maxRuleApplications := 100, warnOnNonterminal := false })
  all_goals first
    | have hr := hnext _ _ h
      simp_all only [mergeHiLayoutFrame]
    | have hr := mergeHiGallopB_layoutFrame _ _ _ hnext _ h
      simp_all only [mergeHiLayoutFrame]
set_option maxHeartbeats 5000000 in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeHiLoop_layoutFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
private lemma mergeHiLoop_layoutFrame
  (fuel : Nat) (cursor : MergeHiCursor κ ν) (result : MergeHiResult κ ν)
  (h : mergeHiLoop? fuel cursor = some result) :
  mergeHiLayoutFrame result.state = mergeHiLayoutFrame cursor.state := by
  induction fuel generalizing cursor result with
  | zero =>
    simp only [mergeHiLoop?] at h
    split at h
    · exact mergeHiSucceed_layoutFrame _ _ h
    · split at h
      · exact mergeHiCopyA_layoutFrame _ _ h
      · have hr := Option.some.inj h
        subst result
        rfl
  | succ fuel ih =>
    simp only [mergeHiLoop?, bind, Option.bind] at h
    by_cases hstop : cursor.na = 0 ∨ cursor.nb = 0
    · rw [if_pos hstop] at h
      exact mergeHiSucceed_layoutFrame _ _ h
    · rw [if_neg hstop] at h
      by_cases hone : cursor.nb = 1
      · rw [if_pos hone] at h
        exact mergeHiCopyA_layoutFrame _ _ h
      · rw [if_neg hone] at h
        cases hphase : cursor.phase with
        | straight aCount bCount =>
          simp only [hphase] at h
          split at h <;> try simp only [reduceCtorEq] at h
          all_goals try split at h <;> try simp only [reduceCtorEq] at h
          all_goals try split at h <;> try simp only [reduceCtorEq] at h
          all_goals try split at h <;> try simp only [reduceCtorEq] at h
          all_goals try aesop (config := {
            enableSimp := false, maxRuleApplications := 100,
            warnOnNonterminal := false })
          all_goals
            have hr := ih _ _ h
            simp_all only [mergeHiLayoutFrame]
        | galloping aCount bCount =>
          simp only [hphase] at h
          exact mergeHiGallopRound_layoutFrame cursor (mergeHiLoop? fuel) ih result h

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeGetmem_layoutFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
private lemma mergeGetmem_layoutFrame (state : MergeState κ ν) (need : PySSize) :
  mergeHiLayoutFrame (mergeGetmem state need).state = mergeHiLayoutFrame state := by
  simp only [mergeGetmem]
  split
  · rfl
  · split <;> simp only
    all_goals simp only [mergeFreemem]
    all_goals split <;> rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeHi_layoutFrame_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHi_layoutFrame_of_eq_some
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {ssa ssb : Int}
  {na nb : Nat}
  {result : MergeHiResult κ ν}
-- given
  (h : mergeHi? state ssa ssb na nb = some result) :
-- imply
  result.state.listlen = state.listlen ∧ result.state.basekeys = state.basekeys ∧ result.state.data.entries.size = state.data.entries.size ∧ result.state.pending = state.pending := by
-- proof
  have hframe : mergeHiLayoutFrame result.state = mergeHiLayoutFrame state := by
    simp only [mergeHi?, bind, Option.bind] at h
    split at h <;> try simp at h
    all_goals try split at h <;> try simp at h
    all_goals try split at h <;> try simp at h
    all_goals try split at h <;> try simp at h
    all_goals aesop (config := { enableSimp := false, warnOnNonterminal := false })
    all_goals
      have hmem := mergeGetmem_layoutFrame state (BitVec.ofNat 64 nb)
      simp_all only [mergeHiLayoutFrame]
  exact
    ⟨congrArg MergeHiLayoutFrame.listlen hframe,
      congrArg MergeHiLayoutFrame.basekeys hframe,
      congrArg MergeHiLayoutFrame.dataSize hframe,
      congrArg MergeHiLayoutFrame.pending hframe⟩

end CPythonListsort

namespace CPythonListsort

/--
[mergeHi_pending_eq_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHi_pending_eq_of_eq_some
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {ssa ssb : Int}
  {na nb : Nat}
  {result : MergeHiResult κ ν}
-- given
  (h : mergeHi? state ssa ssb na nb = some result) :
-- imply
  result.state.pending = state.pending :=
-- proof
  (mergeHi_layoutFrame_of_eq_some state ssa ssb na nb result h).2.2.2

end CPythonListsort

namespace CPythonListsort

/--
[mergeHi_gallop_stability_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHi_gallop_stability_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (mergeHi? mergeHiGallopStabilityRegressionState 0 4 4 3).map (fun result => (result.returnCode, result.fuelExhausted, result.state.data.entries.toList)) = some (0, false, [{ key := 1, value := some 11 }, { key := 2, value := some 20 }, { key := 4, value := some 40 }, { key := 4, value := some 41 }, { key := 5, value := some 51 }, { key := 6, value := some 60 }, { key := 8, value := some 80 }]) := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[mergeHi_inconsistentComparator_nbZero_succeed_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
lemma mergeHi_inconsistentComparator_nbZero_succeed_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  mergeHiNbZeroHedgeRegressionState.key_compare 1 1 = true ∧ (initializedTempPrefix? mergeHiNbZeroHedgeRegressionState.a 2).bind (fun temp => gallopLeft? mergeHiNbZeroHedgeRegressionState temp 0 3 2 1) = some { index := 0, fuelExhausted := false } ∧ (initializedTempPrefix? mergeHiNbZeroHedgeStrictControlState.a 2).bind (fun temp => gallopLeft? mergeHiNbZeroHedgeStrictControlState temp 0 3 2 1) = some { index := 2, fuelExhausted := false } ∧ (mergeHiGallopB? mergeHiNbZeroHedgeRegressionCursor 0 (mergeHiLoop? 1)).map (fun result => (result.returnCode, result.fuelExhausted, result.state.data.entries.toList)) = some (0, false, [{ key := 3, value := some 30 }, { key := 1, value := some 10 }, { key := 2, value := some 20 }]) ∧ (mergeHiGallopB? mergeHiNbZeroHedgeStrictControlCursor 0 (mergeHiLoop? 1)).map (fun result => (result.returnCode, result.fuelExhausted, result.state.data.entries.toList)) = some (0, false, [{ key := 1, value := some 10 }, { key := 2, value := some 20 }, { key := 3, value := some 30 }]) := by
-- proof
  decide

end CPythonListsort

/--
[mergeHi_memcpyCallsite_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean)
-/
@[path]
private lemma mergeHi_memcpyCallsite_distinct_eq
  {κ : Type u}
  {ν : Type v}
  {site : MergeHiMemcpyCallsite} :
-- imply
  site.backings.Distinct := by
-- proof
  apply CPythonListsort.mergeHi_memcpyCallsite_distinct site


-- created on 2026-10-23

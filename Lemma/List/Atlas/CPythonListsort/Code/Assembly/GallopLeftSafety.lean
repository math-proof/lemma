import Mathlib
import sympy.Basic
import Def.CPythonListsort.Code.Assembly.GallopSafety
import Def.CPythonListsort.Code.Transcription.MergeHi.Part6


namespace CPythonListsort

/--
[initializedTempPrefix_agreesWithSlice_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopLeftSafety.lean)
-/
@[path]
lemma initializedTempPrefix_agreesWithSlice_of_eq_some
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {count : Nat}
  {slice : SortSlice κ ν}
-- given
  (hresult : initializedTempPrefix? storage count = some slice) :
-- imply
  (GallopKeySource.temporary storage 0).AgreesWithSlice slice 0 count := by
-- proof
  apply GallopKeySource.temporary_agreesWithSlice_of_entries
    storage 0 count slice
  simpa using
    (initializedTempPrefix_cells_of_eq_some storage count slice hresult).2

end CPythonListsort

namespace CPythonListsort

/--
[gallopLeft_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopLeftSafety.lean)
-/
@[path]
lemma gallopLeft_safe
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {source : GallopKeySource κ ν}
  {slice : SortSlice κ ν}
  {sliceBase : Int}
  {key : κ}
-- given
  (n hint : Nat)
  (hvalid : source.ValidRange n)
  (hlive : source.Live)
  (hagrees : source.AgreesWithSlice slice sliceBase n)
  (hn : 0 < n)
  (hhint : hint < n)
  (hnmax : n ≤ PY_LIST_MAX) :
-- imply
  ∃ result, (gallopLeftTraced? state source key n hint).result = some result ∧ result.fuelExhausted = false ∧ result.index ≤ n ∧ (gallopLeftTraced? state source key n hint).trace.fuelExhausted = false ∧ (gallopLeftTraced? state source key n hint).trace.pushDepths = [] ∧ (gallopLeftTraced? state source key n hint).trace.allAccessesInBounds ∧ (gallopLeftTraced? state source key n hint).trace.tempPayloadAccessesLive ∧ (gallopLeftTraced? state source key n hint).erase = gallopLeft? state slice sliceBase key n hint := by
-- proof
  rcases gallopLeftFromSource_safe state source key n hint hvalid hlive hn hhint
    hnmax with
    ⟨result, hresult, hnotExhausted, hbound,
      htraceFuel, htracePushes, htraceBounds, htraceLive⟩
  exact ⟨result, hresult, hnotExhausted, hbound, htraceFuel, htracePushes,
    htraceBounds, htraceLive, erase_gallopLeftTraced_eq_slice state source slice
      sliceBase key n hint hvalid hagrees hn hhint hnmax⟩

end CPythonListsort

namespace CPythonListsort

/--
[gallopLeft_main_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopLeftSafety.lean)
-/
@[path]
lemma gallopLeft_main_safe
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {slice : SortSlice κ ν}
  {base : Int}
  {key : κ}
-- given
  (n hint : Nat)
  (hvalid : (GallopKeySource.main slice base).ValidRange n)
  (hn : 0 < n)
  (hhint : hint < n)
  (hnmax : n ≤ PY_LIST_MAX) :
-- imply
  ∃ result, (gallopLeftTraced? state (.main slice base) key n hint).result = some result ∧ result.fuelExhausted = false ∧ result.index ≤ n ∧ (gallopLeftTraced? state (.main slice base) key n hint).trace.fuelExhausted = false ∧ (gallopLeftTraced? state (.main slice base) key n hint).trace.pushDepths = [] ∧ (gallopLeftTraced? state (.main slice base) key n hint).trace.allAccessesInBounds ∧ (gallopLeftTraced? state (.main slice base) key n hint).trace.tempPayloadAccessesLive ∧ (gallopLeftTraced? state (.main slice base) key n hint).erase = gallopLeft? state slice base key n hint := by
-- proof
  exact gallopLeft_safe state (.main slice base) slice base key n hint hvalid
    trivial (GallopKeySource.main_agreesWithSlice slice base n) hn hhint hnmax

end CPythonListsort

namespace CPythonListsort

/--
[gallopLeft_temporary_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopLeftSafety.lean)
-/
@[path]
lemma gallopLeft_temporary_safe
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {storage : TempStorage κ ν}
  {sourceBase : Int}
  {slice : SortSlice κ ν}
  {sliceBase : Int}
  {key : κ}
-- given
  (n hint : Nat)
  (hvalid : (GallopKeySource.temporary storage sourceBase).ValidRange n)
  (hlive : storage.Live)
  (hagrees : (GallopKeySource.temporary storage sourceBase).AgreesWithSlice slice sliceBase n)
  (hn : 0 < n)
  (hhint : hint < n)
  (hnmax : n ≤ PY_LIST_MAX) :
-- imply
  let execution := gallopLeftTraced? state (.temporary storage sourceBase) key n hint ∃ result, execution.result = some result ∧ result.fuelExhausted = false ∧ result.index ≤ n ∧ execution.trace.fuelExhausted = false ∧ execution.trace.pushDepths = [] ∧ execution.trace.allAccessesInBounds ∧ execution.trace.tempPayloadAccessesLive ∧ execution.erase = gallopLeft? state slice sliceBase key n hint := by
-- proof
  exact gallopLeft_safe state (.temporary storage sourceBase) slice sliceBase
    key n hint hvalid hlive hagrees hn hhint hnmax

end CPythonListsort


-- created on 2026-10-23

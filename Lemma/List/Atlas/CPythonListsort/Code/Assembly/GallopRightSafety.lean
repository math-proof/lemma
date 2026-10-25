import Mathlib
import sympy.Basic
import Def.CPythonListsort.Code.Assembly.GallopSafety
import Def.CPythonListsort.Code.Transcription.MergeLo.Part6


namespace CPythonListsort

/--
[tempRun_agreesWithSlice_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopRightSafety.lean)
-/
@[path]
lemma tempRun_agreesWithSlice_of_eq_some
  {κ : Type u}
  {ν : Type v}
  {storage : TempStorage κ ν}
  {start count : Nat}
  {slice : SortSlice κ ν}
-- given
  (hresult : tempRun? storage start count = some slice) :
-- imply
  (GallopKeySource.temporary storage (Int.ofNat start)).AgreesWithSlice slice 0 count :=
-- proof
  GallopKeySource.temporary_agreesWithSlice_of_entries storage start count
    slice (tempRun_cells_of_eq_some storage start count slice hresult).2

end CPythonListsort

namespace CPythonListsort

/--
[gallopRight_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopRightSafety.lean)
-/
@[path]
lemma gallopRight_safe
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
  ∃ result, (gallopRightTraced? state source key n hint).result = some result ∧ result.fuelExhausted = false ∧ result.index ≤ n ∧ (gallopRightTraced? state source key n hint).trace.fuelExhausted = false ∧ (gallopRightTraced? state source key n hint).trace.pushDepths = [] ∧ (gallopRightTraced? state source key n hint).trace.allAccessesInBounds ∧ (gallopRightTraced? state source key n hint).trace.tempPayloadAccessesLive ∧ (gallopRightTraced? state source key n hint).erase = gallopRight? state slice sliceBase key n hint := by
-- proof
  rcases gallopRightFromSource_safe state source key n hint hvalid hlive hn hhint
    hnmax with
    ⟨result, hresult, hnotExhausted, hbound,
      htraceFuel, htracePushes, htraceBounds, htraceLive⟩
  exact ⟨result, hresult, hnotExhausted, hbound, htraceFuel, htracePushes,
    htraceBounds, htraceLive, erase_gallopRightTraced_eq_slice state source slice
      sliceBase key n hint hvalid hagrees hn hhint hnmax⟩

end CPythonListsort

namespace CPythonListsort

/--
[gallopRight_main_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopRightSafety.lean)
-/
@[path]
lemma gallopRight_main_safe
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
  ∃ result, (gallopRightTraced? state (.main slice base) key n hint).result = some result ∧ result.fuelExhausted = false ∧ result.index ≤ n ∧ (gallopRightTraced? state (.main slice base) key n hint).trace.fuelExhausted = false ∧ (gallopRightTraced? state (.main slice base) key n hint).trace.pushDepths = [] ∧ (gallopRightTraced? state (.main slice base) key n hint).trace.allAccessesInBounds ∧ (gallopRightTraced? state (.main slice base) key n hint).trace.tempPayloadAccessesLive ∧ (gallopRightTraced? state (.main slice base) key n hint).erase = gallopRight? state slice base key n hint := by
-- proof
  exact gallopRight_safe state (.main slice base) slice base key n hint hvalid
    trivial (GallopKeySource.main_agreesWithSlice slice base n) hn hhint hnmax

end CPythonListsort

namespace CPythonListsort

/--
[gallopRight_temporary_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopRightSafety.lean)
-/
@[path]
lemma gallopRight_temporary_safe
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
  let execution := gallopRightTraced? state (.temporary storage sourceBase) key n hint ∃ result, execution.result = some result ∧ result.fuelExhausted = false ∧ result.index ≤ n ∧ execution.trace.fuelExhausted = false ∧ execution.trace.pushDepths = [] ∧ execution.trace.allAccessesInBounds ∧ execution.trace.tempPayloadAccessesLive ∧ execution.erase = gallopRight? state slice sliceBase key n hint := by
-- proof
  exact gallopRight_safe state (.temporary storage sourceBase) slice sliceBase
    key n hint hvalid hlive hagrees hn hhint hnmax

end CPythonListsort


-- created on 2026-10-23

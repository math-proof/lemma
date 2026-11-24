/- Lifted from Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety. -/

module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.List.Atlas.CPythonListsort.Code.Assembly.GallopSafety
public import Def.CPythonListsort.Code.Assembly.GallopSafety

public section

open CPythonListsort

namespace CPythonListsort

open GallopKeySource

/-- Wrapper around `gallopRightFromSource_safe` plus the slice-erase equation. -/
public theorem gallopRight_safe
  {κ : Type u} {ν : Type v}
  (state : MergeState κ ν) (source : GallopKeySource κ ν)
  (slice : SortSlice κ ν) (sliceBase : Int) (key : κ)
  (n hint : Nat)
  (hvalid : source.ValidRange n)
  (hlive : source.Live)
  (hagrees : source.AgreesWithSlice slice sliceBase n)
  (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
  ∃ result,
    (gallopRightTraced? state source key n hint).result = some result ∧
      result.fuelExhausted = false ∧ result.index ≤ n ∧
      (gallopRightTraced? state source key n hint).trace.fuelExhausted = false ∧
      (gallopRightTraced? state source key n hint).trace.pushDepths = [] ∧
      (gallopRightTraced? state source key n hint).trace.allAccessesInBounds ∧
      (gallopRightTraced? state source key n hint).trace.tempPayloadAccessesLive ∧
      (gallopRightTraced? state source key n hint).erase =
        gallopRight? state slice sliceBase key n hint := by
  rcases gallopRightFromSource_safe state source key n hint hvalid hlive hn hhint
    hnmax with ⟨result, hresult, hnotExhausted, hbound, hsafe⟩
  have ⟨htraceFuel, htracePushes, htraceBounds, htraceLive⟩ :=
    show GallopTraceSafe (gallopRightTraced? state source key n hint) from hsafe
  exact ⟨result, hresult, hnotExhausted, hbound, htraceFuel, htracePushes,
    htraceBounds, htraceLive, erase_gallopRightTraced_eq_slice state source slice
      sliceBase key n hint hvalid hagrees hn hhint hnmax⟩

/-- Specialization of `gallopRight_safe` to a main-array key source. -/
public theorem gallopRight_main_safe
  {κ : Type u} {ν : Type v}
  (state : MergeState κ ν) (slice : SortSlice κ ν) (base : Int) (key : κ)
  (n hint : Nat)
  (hvalid : (GallopKeySource.main slice base).ValidRange n)
  (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
  ∃ result,
    (gallopRightTraced? state (.main slice base) key n hint).result =
      some result ∧
      result.fuelExhausted = false ∧ result.index ≤ n ∧
      (gallopRightTraced? state (.main slice base) key n hint).trace.fuelExhausted =
        false ∧
      (gallopRightTraced? state (.main slice base) key n hint).trace.pushDepths =
        [] ∧
      (gallopRightTraced? state (.main slice base) key n hint).trace.allAccessesInBounds ∧
      (gallopRightTraced? state (.main slice base) key n hint).trace.tempPayloadAccessesLive ∧
      (gallopRightTraced? state (.main slice base) key n hint).erase =
        gallopRight? state slice base key n hint := by
  exact gallopRight_safe state (.main slice base) slice base key n hint hvalid
    trivial GallopKeySource.main_agreesWithSlice hn hhint hnmax

end CPythonListsort

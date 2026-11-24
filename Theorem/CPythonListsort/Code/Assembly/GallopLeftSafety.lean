/- Lifted from Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety. -/

module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.List.Atlas.CPythonListsort.Code.Assembly.GallopSafety
public import Def.CPythonListsort.Code.Assembly.GallopSafety
public section

open CPythonListsort

namespace CPythonListsort

open GallopKeySource

/-- Wrapper around `gallopLeftFromSource_safe` plus the slice-erase equation. -/
public theorem gallopLeft_safe
  {κ : Type u} {ν : Type v}
  (state : MergeState κ ν) (source : GallopKeySource κ ν)
  (slice : SortSlice κ ν) (sliceBase : Int) (key : κ)
  (n hint : Nat)
  (hvalid : source.ValidRange n)
  (hlive : source.Live)
  (hagrees : source.AgreesWithSlice slice sliceBase n)
  (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
  ∃ result,
    (gallopLeftTraced? state source key n hint).result = some result ∧
      result.fuelExhausted = false ∧ result.index ≤ n ∧
      (gallopLeftTraced? state source key n hint).trace.fuelExhausted = false ∧
      (gallopLeftTraced? state source key n hint).trace.pushDepths = [] ∧
      (gallopLeftTraced? state source key n hint).trace.allAccessesInBounds ∧
      (gallopLeftTraced? state source key n hint).trace.tempPayloadAccessesLive ∧
      (gallopLeftTraced? state source key n hint).erase =
        gallopLeft? state slice sliceBase key n hint := by
  rcases gallopLeftFromSource_safe state source key n hint hvalid hlive hn hhint
    hnmax with ⟨result, hresult, hnotExhausted, hbound, hsafe⟩
  have ⟨htraceFuel, htracePushes, htraceBounds, htraceLive⟩ :=
    show GallopTraceSafe (gallopLeftTraced? state source key n hint) from hsafe
  exact ⟨result, hresult, hnotExhausted, hbound, htraceFuel, htracePushes,
    htraceBounds, htraceLive, erase_gallopLeftTraced_eq_slice state source slice
      sliceBase key n hint hvalid hagrees hn hhint hnmax⟩

/-- Specialization of `gallopLeft_safe` to a main-array key source. -/
public theorem gallopLeft_main_safe
  {κ : Type u} {ν : Type v}
  (state : MergeState κ ν) (slice : SortSlice κ ν) (base : Int) (key : κ)
  (n hint : Nat)
  (hvalid : (GallopKeySource.main slice base).ValidRange n)
  (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
  ∃ result,
    (gallopLeftTraced? state (.main slice base) key n hint).result =
      some result ∧
      result.fuelExhausted = false ∧ result.index ≤ n ∧
      (gallopLeftTraced? state (.main slice base) key n hint).trace.fuelExhausted =
        false ∧
      (gallopLeftTraced? state (.main slice base) key n hint).trace.pushDepths =
        [] ∧
      (gallopLeftTraced? state (.main slice base) key n hint).trace.allAccessesInBounds ∧
      (gallopLeftTraced? state (.main slice base) key n hint).trace.tempPayloadAccessesLive ∧
      (gallopLeftTraced? state (.main slice base) key n hint).erase =
        gallopLeft? state slice base key n hint := by
  exact gallopLeft_safe state (.main slice base) slice base key n hint hvalid
    trivial GallopKeySource.main_agreesWithSlice hn hhint hnmax

end CPythonListsort

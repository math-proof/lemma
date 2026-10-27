import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
open CPythonListsort


namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[pair_geometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemRequestBound.lean)
-/
@[path]
cover. -/
private lemma PendingRunsCover.pair_geometry
  {cursor limit : Nat} {before after : List PendingRun}
  {left right : PendingRun}
  (hcover :
    PendingRunsCover cursor limit (before ++ left :: right :: after)) :
  cursor ≤ left.base ∧
    left.len.Nonnegative ∧ 0 < left.len.toNat ∧
    left.endIndex = right.base ∧
    right.len.Nonnegative ∧ 0 < right.len.toNat ∧
    right.endIndex ≤ limit := by
  induction before generalizing cursor with
  | nil =>
    simp only [List.nil_append, PendingRunsCover] at hcover
    rcases hcover with
      ⟨hleftBase, hleftNonnegative, hleftPositive, _hleftEnd,
        hrightBase, hrightNonnegative, hrightPositive, hrightEnd, _⟩
    exact
      ⟨by omega, hleftNonnegative, hleftPositive, hrightBase.symm,
        hrightNonnegative, hrightPositive, hrightEnd⟩
  | cons head before ih =>
    simp only [List.cons_append, PendingRunsCover] at hcover
    rcases hcover with
      ⟨hheadBase, _hheadNonnegative, hheadPositive, _hheadEnd, htail⟩
    rcases ih htail with
      ⟨hleftBase, hleftNonnegative, hleftPositive, hadjacent,
        hrightNonnegative, hrightPositive, hrightEnd⟩
    have hcursor : cursor ≤ left.base := by
      simp only [PendingRun.endIndex] at hleftBase
      omega
    exact
      ⟨hcursor, hleftNonnegative, hleftPositive, hadjacent,
        hrightNonnegative, hrightPositive, hrightEnd⟩

end CPythonListsort

namespace CPythonListsort

/--
[PendingLayout.adjacentPair_geometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemRequestBound.lean)
-/
@[path]
lemma PendingLayout.adjacentPair_geometry
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {scanned i : Nat}
  {left right : PendingRun}
-- given
  (hlayout : PendingLayout state scanned)
  (hleft : state.pending[i]? = some left)
  (hright : state.pending[i + 1]? = some right) :
-- imply
  PendingAdjacentPairGeometry state scanned left right := by
-- proof
  rcases Array.exists_pair_split_of_getElem?_eq_some hleft hright with
    ⟨before, after, _hbefore, hsplit⟩
  have hcover :
    PendingRunsCover state.basekeys (state.basekeys + scanned)
      (before ++ left :: right :: after) := by
    simpa [hsplit] using hlayout.2.2.2
  rcases hcover.pair_geometry with
    ⟨hleftBase, hleftNonnegative, hleftPositive, hadjacent,
      hrightNonnegative, hrightPositive, hrightEnd⟩
  have htotal := hcover.totalLength
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at htotal
  have hpairSpan : left.len.toNat + right.len.toNat ≤ scanned := by
    omega
  exact
    ⟨hleftBase, hleftNonnegative, hleftPositive, hadjacent,
      hrightNonnegative, hrightPositive, hrightEnd, hpairSpan,
      hlayout.2.2.1⟩

end CPythonListsort

namespace CPythonListsort

/--
[PendingLayout.adjacentPair_span](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemRequestBound.lean)
-/
@[path]
lemma PendingLayout.adjacentPair_span
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {scanned i : Nat}
  {left right : PendingRun}
-- given
  (hlayout : PendingLayout state scanned)
  (hleft : state.pending[i]? = some left)
  (hright : state.pending[i + 1]? = some right) :
-- imply
  left.len.toNat + right.len.toNat ≤ scanned :=
-- proof
  (hlayout.adjacentPair_geometry hleft hright).pairSpan

end CPythonListsort

namespace CPythonListsort

/--
[GallopKeySource.main_validRange_of_base_add_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemRequestBound.lean)
-/
@[path]
lemma GallopKeySource.main_validRange_of_base_add_le
  {κ : Type u}
  {ν : Type v}
  {slice : SortSlice κ ν}
  {base n : Nat}
-- given
  (hbound : base + n ≤ slice.entries.size) :
-- imply
  (GallopKeySource.main slice (Int.ofNat base)).ValidRange n := by
-- proof
  refine ⟨?_, ?_, ?_⟩
  · simp only [GallopKeySource.base, Int.ofNat_eq_natCast]
    exact Int.natCast_nonneg base
  · simp only [GallopKeySource.base, GallopKeySource.extent,
    Int.ofNat_eq_natCast]
    exact_mod_cast hbound
  · intro j hj
    have hindex : base + j < slice.entries.size := by omega
    refine ⟨slice.entries[base + j], ?_⟩
    change slice.read? (Int.ofNat base + Int.ofNat j) =
      some slice.entries[base + j]
    rw [SortSlice.read?]
    split
    · rw [show (Int.ofNat base + Int.ofNat j).toNat = base + j by rfl]
      exact Array.getElem?_eq_getElem hindex
    · rename_i hnegative
      exfalso
      apply hnegative
      exact add_nonneg (Int.natCast_nonneg base) (Int.natCast_nonneg j)

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mainRun_validRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemRequestBound.lean)
-/
@[path]
private lemma mainRun_validRange
  (pre call : MergeState κ ν) (scanned : Nat) (run : PendingRun)
  (hlayout : PendingLayout pre scanned)
  (hdata : call.data = pre.data)
  (_hbase : pre.basekeys ≤ run.base)
  (hend : run.endIndex ≤ pre.basekeys + scanned) :
  (GallopKeySource.main call.data (Int.ofNat run.base)).ValidRange
    run.len.toNat := by
  have hendData : run.base + run.len.toNat ≤ pre.data.entries.size := by
    have hscanEnd : pre.basekeys + scanned ≤ pre.basekeys + pre.listlen.toNat :=
      Nat.add_le_add_left hlayout.2.2.1 pre.basekeys
    simpa only [PendingRun.endIndex] using
      hend.trans (hscanEnd.trans hlayout.2.1)
  apply GallopKeySource.main_validRange_of_base_add_le
  rwa [hdata]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[ofNat64_toNat_of_le_pyListMax](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemRequestBound.lean)
-/
@[path]
private lemma ofNat64_toNat_of_le_pyListMax {x : Nat}
  (hx : x ≤ PY_LIST_MAX) :
  (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hx ⊢
  omega

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[ofNat64_nonnegative_of_le_pyListMax](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemRequestBound.lean)
-/
@[path]
private lemma ofNat64_nonnegative_of_le_pyListMax {x : Nat}
  (hx : x ≤ PY_LIST_MAX) :
  PySSize.Nonnegative (BitVec.ofNat 64 x) := by
  rw [PySSize.Nonnegative, BitVec.msb_eq_false_iff_two_mul_lt]
  rw [ofNat64_toNat_of_le_pyListMax hx]
  norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hx ⊢
  omega

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeGetmem_not_guardRejected_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemRequestBound.lean)
-/
@[path]
private lemma mergeGetmem_not_guardRejected_of_le
  (state : MergeState κ ν) (need : PySSize)
  (hlimit : need.toNat ≤ mergeGetmemAllocationLimit state.a) :
  (mergeGetmem state need).outcome ≠ .guardRejected := by
  by_cases hreuse : need.sle state.alloced = true
  · simp [mergeGetmem, hreuse]
  · have hreuseFalse : need.sle state.alloced = false :=
    Bool.eq_false_of_not_eq_true hreuse
    simp [mergeGetmem, hreuseFalse, Nat.not_lt.mpr hlimit]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[requestBound_of_callsiteEvidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemRequestBound.lean)
-/
@[path]
private lemma requestBound_of_callsiteEvidence
  (pre : MergeState κ ν) (scanned i requested : Nat)
  (call : MergeAtCall κ ν)
  (hlayout : PendingLayout pre scanned)
  (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
  (hevidence : MergeAtCallsiteEvidence pre i call)
  (hdispatch :
    (requested = call.na ∧ call.na ≤ call.nb) ∨
      (requested = call.nb ∧ call.nb < call.na)) :
  MergeGetmemRequestBoundFacts pre scanned i requested call := by
  have hgeometry := hlayout.adjacentPair_geometry
    hevidence.leftSelected hevidence.rightSelected
  have hleftPositive := hgeometry.leftPositive
  have hrightPositive := hgeometry.rightPositive
  have hpairSpan := hgeometry.pairSpan
  have hscannedBound := hgeometry.scannedBound
  have hleftEnd :
    call.left.endIndex ≤ pre.basekeys + scanned := by
    calc
      call.left.endIndex = call.right.base := hgeometry.adjacent
      _ ≤ call.right.endIndex := by simp [PendingRun.endIndex]
      _ ≤ pre.basekeys + scanned := hgeometry.rightEnd
  have hleftValid := mainRun_validRange pre call.state scanned call.left
    hlayout hevidence.data_eq hgeometry.leftBase
    hleftEnd
  have hrightBase : pre.basekeys ≤ call.right.base := by
    calc
      pre.basekeys ≤ call.left.base := hgeometry.leftBase
      _ ≤ call.left.endIndex := by simp [PendingRun.endIndex]
      _ = call.right.base := hgeometry.adjacent
  have hrightValid := mainRun_validRange pre call.state scanned call.right
    hlayout hevidence.data_eq hrightBase hgeometry.rightEnd
  have hleftMax : call.left.len.toNat ≤ PY_LIST_MAX := by
    omega
  have hrightMax : call.right.len.toNat ≤ PY_LIST_MAX := by
    omega
  rcases gallopRight_main_safe call.state call.state.data
    (Int.ofNat call.left.base) call.firstB.key call.left.len.toNat 0
    hleftValid hleftPositive (by omega) hleftMax with
    ⟨rightResult, hrightResult, _hrightFuel, hrightBound,
      _hrightTraceFuel, _hrightTracePushes, _hrightTraceBounds,
      _hrightTraceLive, hrightErase⟩
  have hrightUntraced :
    gallopRight? call.state call.state.data (Int.ofNat call.left.base)
      call.firstB.key call.left.len.toNat 0 = some rightResult := by
    rw [← hrightErase]
    simpa [TraceResult.erase] using hrightResult
  have htrimAEq : rightResult = call.trimA := by
    rw [hevidence.rightGallop] at hrightUntraced
    exact Option.some.inj hrightUntraced.symm
  have htrimABound : call.trimA.index ≤ call.left.len.toNat := by
    simpa [htrimAEq] using hrightBound
  rcases gallopLeft_main_safe call.state call.state.data
    (Int.ofNat call.right.base) call.lastA.key call.right.len.toNat
    (call.right.len.toNat - 1) hrightValid hrightPositive
    (by omega) hrightMax with
    ⟨leftResult, hleftResult, _hleftFuel, hleftBound,
      _hleftTraceFuel, _hleftTracePushes, _hleftTraceBounds,
      _hleftTraceLive, hleftErase⟩
  have hleftUntraced :
    gallopLeft? call.state call.state.data (Int.ofNat call.right.base)
      call.lastA.key call.right.len.toNat (call.right.len.toNat - 1) =
        some leftResult := by
    rw [← hleftErase]
    simpa [TraceResult.erase] using hleftResult
  have htrimBEq : leftResult = call.trimB := by
    rw [hevidence.leftGallop] at hleftUntraced
    exact Option.some.inj hleftUntraced.symm
  have htrimBBound : call.trimB.index ≤ call.right.len.toNat := by
    simpa [htrimBEq] using hleftBound
  have hleftAccounting :
    call.na + call.trimA.index = call.left.len.toNat := by
    rw [hevidence.leftRemainder]
    exact Nat.sub_add_cancel htrimABound
  have hleftTrimmed : call.na ≤ call.left.len.toNat := by
    omega
  have hrightTrimmed : call.nb ≤ call.right.len.toNat := by
    rwa [hevidence.rightRemainder]
  have htrimmedPair :
    call.na + call.nb ≤ call.left.len.toNat + call.right.len.toNat := by
    omega
  have hremainingList : call.na + call.nb ≤ pre.listlen.toNat := by
    omega
  have hrequestMin : requested = min call.na call.nb := by
    obtain hdispatch | hdispatch := hdispatch
    · rw [hdispatch.1, Nat.min_eq_left hdispatch.2]
    · rw [hdispatch.1, Nat.min_eq_right (Nat.le_of_lt hdispatch.2)]
  have hrequestHalf : requested ≤ (call.na + call.nb) / 2 := by
    obtain hdispatch | hdispatch := hdispatch
    · rw [hdispatch.1]
      omega
    · rw [hdispatch.1]
      omega
  have hhalfList :
    (call.na + call.nb) / 2 ≤ pre.listlen.toNat / 2 :=
    Nat.div_le_div_right hremainingList
  have hrequestMax : requested ≤ PY_LIST_MAX := by
    omega
  have hroundtrip := ofNat64_toNat_of_le_pyListMax hrequestMax
  have hnonnegative := ofNat64_nonnegative_of_le_pyListMax hrequestMax
  have hkeyed : call.state.a.hasValues = true →
    mergeGetmemAllocationLimit call.state.a =
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES / 2 ∧
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES / 2 = 2 ^ 59 - 1 := by
    intro hvalues
    constructor
    · simp [mergeGetmemAllocationLimit, TempStorage.multiplier, hvalues]
    · norm_num [PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]
  have hunkeyed : call.state.a.hasValues = false →
    mergeGetmemAllocationLimit call.state.a =
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES ∧
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES = 2 ^ 60 - 1 := by
    intro hvalues
    constructor
    · simp [mergeGetmemAllocationLimit, TempStorage.multiplier, hvalues]
    · norm_num [PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]
  have hrequestLimit :
    (BitVec.ofNat 64 requested).toNat ≤
      mergeGetmemAllocationLimit call.state.a := by
    rw [hroundtrip]
    cases hvalues : call.state.a.hasValues with
    | false =>
      rw [(hunkeyed hvalues).1, (hunkeyed hvalues).2]
      norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hmax
      omega
    | true =>
      rw [(hkeyed hvalues).1, (hkeyed hvalues).2]
      norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hmax
      omega
  exact
    { leftSelected := hevidence.leftSelected
      rightSelected := hevidence.rightSelected
      storageFrame := hevidence.storage_eq
      listlenFrame := hevidence.listlen_eq
      hasValuesFrame := hevidence.hasValues_eq
      allocedFrame := hevidence.alloced_eq
      firstGallopBound := htrimABound
      secondGallopBound := htrimBBound
      leftTrimAccounting := hleftAccounting
      leftTrimmed := hleftTrimmed
      rightTrimmed := hrightTrimmed
      runLengthChain :=
        ⟨htrimmedPair, hgeometry.pairSpan, hgeometry.scannedBound⟩
      sourceDispatch := hdispatch
      requestIsMinimum := hrequestMin
      requestRoundtrip := hroundtrip
      requestNonnegative := hnonnegative
      smallerHalfChain := ⟨hrequestHalf, hhalfList⟩
      requestWordHalfChain := ⟨by simpa [hroundtrip] using hrequestHalf, hhalfList⟩
      keyedLimit := hkeyed
      unkeyedLimit := hunkeyed
      requestWithinLimit := hrequestLimit
      guardNotRejected :=
        mergeGetmem_not_guardRejected_of_le call.state _ hrequestLimit }

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeAtSafetyGeometry_of_evidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemRequestBound.lean)
-/
@[path]
private lemma mergeAtSafetyGeometry_of_evidence
  (pre : MergeState κ ν) (scanned i requested : Nat)
  (call : MergeAtCall κ ν)
  (hlayout : PendingLayout pre scanned)
  (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
  (hevidence : MergeAtCallsiteEvidence pre i call)
  (hfacts : MergeGetmemRequestBoundFacts pre scanned i requested call) :
  MergeAtSafetyGeometry pre scanned i call := by
  have hgeometry := hlayout.adjacentPair_geometry
    hevidence.leftSelected hevidence.rightSelected
  have hscanData : pre.basekeys + scanned ≤ pre.data.entries.size := by
    exact (Nat.add_le_add_left hlayout.2.2.1 pre.basekeys).trans hlayout.2.1
  have hrightEndData :
    call.right.base + call.right.len.toNat ≤ pre.data.entries.size := by
    simpa only [PendingRun.endIndex] using hgeometry.rightEnd.trans hscanData
  have hssaNaNat :
    call.left.base + call.trimA.index + call.na = call.right.base := by
    have hadjacent :
      call.left.base + call.left.len.toNat = call.right.base := by
      simpa only [PendingRun.endIndex] using hgeometry.adjacent
    have hleftAccounting := hfacts.leftTrimAccounting
    omega
  have hrightNat :
    call.right.base + call.nb ≤ call.state.data.entries.size := by
    rw [hevidence.data_eq]
    exact
      (Nat.add_le_add_left hfacts.rightTrimmed call.right.base).trans
        hrightEndData
  have hmergedNat :
    call.left.base + call.trimA.index + (call.na + call.nb) ≤
      call.state.data.entries.size := by
    calc
      call.left.base + call.trimA.index + (call.na + call.nb) =
        call.right.base + call.nb := by omega
      _ ≤ call.state.data.entries.size := hrightNat
  have hrunLength : call.na + call.nb ≤ pre.listlen.toNat := by
    obtain ⟨htrimmed, hspan, hscan⟩ := hfacts.runLengthChain
    omega
  have hlistWord : PY_LIST_MAX ≤ PY_SSIZE_T_MAX := by
    norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]
  refine
    { evidence := hevidence
      ssaNonnegative := ?_
      ssbNonnegative := ?_
      adjacent := ?_
      mergedRange := ?_
      rightRange := ?_
      leftPositive := hevidence.leftPositive
      rightPositive := hevidence.rightPositive
      leftWordBound := by omega
      rightWordBound := by omega
      runLengthBound := hrunLength }
  · rw [hevidence.ssa_eq]
    exact Int.natCast_nonneg _
  · rw [hevidence.ssb_eq]
    exact Int.natCast_nonneg _
  · rw [hevidence.ssa_eq, hevidence.ssb_eq]
    simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using
      congrArg (fun n : Nat => (n : Int)) hssaNaNat
  · rw [hevidence.ssa_eq]
    simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using
      (Int.ofNat_le.mpr hmergedNat)
  · rw [hevidence.ssb_eq]
    simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using
      (Int.ofNat_le.mpr hrightNat)

end CPythonListsort

namespace CPythonListsort

/--
[mergeGetmem_lo_request_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemRequestBound.lean)
-/
@[path]
lemma mergeGetmem_lo_request_bound
  {κ : Type u}
  {ν : Type v}
  {pre : MergeState κ ν}
  {scanned i : Nat}
  {call : MergeAtCall κ ν}
-- given
  (hlayout : PendingLayout pre scanned)
  (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
  (hprepare : prepareMergeAt? pre i = some (.mergeLo call)) :
-- imply
  MergeGetmemRequestBoundFacts pre scanned i call.na call := by
-- proof
  rcases prepareMergeAt_lo_callsite_of_eq_some pre i call hprepare with
    ⟨hevidence, hdispatch⟩
  exact requestBound_of_callsiteEvidence pre scanned i call.na call hlayout hmax
    hevidence (Or.inl ⟨rfl, hdispatch⟩)

end CPythonListsort

namespace CPythonListsort

/--
[mergeGetmem_hi_request_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemRequestBound.lean)
-/
@[path]
lemma mergeGetmem_hi_request_bound
  {κ : Type u}
  {ν : Type v}
  {pre : MergeState κ ν}
  {scanned i : Nat}
  {call : MergeAtCall κ ν}
-- given
  (hlayout : PendingLayout pre scanned)
  (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
  (hprepare : prepareMergeAt? pre i = some (.mergeHi call)) :
-- imply
  MergeGetmemRequestBoundFacts pre scanned i call.nb call := by
-- proof
  rcases prepareMergeAt_hi_callsite_of_eq_some pre i call hprepare with
    ⟨hevidence, hdispatch⟩
  exact requestBound_of_callsiteEvidence pre scanned i call.nb call hlayout hmax
    hevidence (Or.inr ⟨rfl, hdispatch⟩)

end CPythonListsort

namespace CPythonListsort

/--
[mergeLo_callsite_safety_geometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemRequestBound.lean)
-/
@[path]
lemma mergeLo_callsite_safety_geometry
  {κ : Type u}
  {ν : Type v}
  {pre : MergeState κ ν}
  {scanned i : Nat}
  {call : MergeAtCall κ ν}
-- given
  (hlayout : PendingLayout pre scanned)
  (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
  (hprepare : prepareMergeAt? pre i = some (.mergeLo call)) :
-- imply
  MergeAtSafetyGeometry pre scanned i call := by
-- proof
  rcases prepareMergeAt_lo_callsite_of_eq_some pre i call hprepare with
    ⟨hevidence, _hdispatch⟩
  exact mergeAtSafetyGeometry_of_evidence pre scanned i call.na call hlayout hmax
    hevidence (mergeGetmem_lo_request_bound pre scanned i call hlayout hmax hprepare)

end CPythonListsort

namespace CPythonListsort

/--
[mergeHi_callsite_safety_geometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemRequestBound.lean)
-/
@[path]
lemma mergeHi_callsite_safety_geometry
  {κ : Type u}
  {ν : Type v}
  {pre : MergeState κ ν}
  {scanned i : Nat}
  {call : MergeAtCall κ ν}
-- given
  (hlayout : PendingLayout pre scanned)
  (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
  (hprepare : prepareMergeAt? pre i = some (.mergeHi call)) :
-- imply
  MergeAtSafetyGeometry pre scanned i call := by
-- proof
  rcases prepareMergeAt_hi_callsite_of_eq_some pre i call hprepare with
    ⟨hevidence, _hdispatch⟩
  exact mergeAtSafetyGeometry_of_evidence pre scanned i call.nb call hlayout hmax
    hevidence (mergeGetmem_hi_request_bound pre scanned i call hlayout hmax hprepare)

end CPythonListsort

namespace CPythonListsort

/--
[mergeGetmem_callsite_request_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemRequestBound.lean)
-/
@[path]
lemma mergeGetmem_callsite_request_bound
  {κ : Type u}
  {ν : Type v} :
-- imply
  MergeGetmemRequestBoundContract κ ν where mergeLo :=
-- proof
  mergeGetmem_lo_request_bound
    mergeHi := mergeGetmem_hi_request_bound
    keyedFencepost := mergeGetmem_keyed_boundary_regression

end CPythonListsort


-- created on 2026-10-23

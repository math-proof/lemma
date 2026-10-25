/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety
import Def.CPythonListsort.Code.Assembly.MergeHiSafety.Part3
/-!
# `merge_hi` traced execution and safety

This module instruments the right-to-left merge directly.  Its evaluator does
not run `mergeHi?` and attach a second, decorative trace: every state transition
is produced by the typed operation that emits its access events.  The three
`memcpy` paths retain their exact source call-site tag and distinct-backing
permit, main-data block movement uses the overlap-safe traced `memmove`, and
temporary gallops read their live storage through `GallopKeySource.temporary`.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

namespace MergeHiStableFrame

namespace MergeHiStorageFrame

namespace MergeHiCursorInvariant

theorem MergeHiCorePost.bind
    (origin : MergeState κ ν) (request : Nat)
    (current : TraceResult α)
    (next : α → TraceResult (MergeHiResult κ ν)) (value : α)
    (reference : Option (MergeHiResult κ ν)) (result : MergeHiResult κ ν)
    (hcurrent : current.result = some value)
    (hcurrentSafe : MovementTraceSafe current)
    (hnext : MergeHiCorePost origin request (next value) reference result)
    (herase : (current.bind next).erase = reference) :
    MergeHiCorePost origin request (current.bind next) reference result := by
  exact
    { resultEq := by
        unfold TraceResult.bind
        rw [hcurrent]
        exact hnext.resultEq
      returnCode := hnext.returnCode
      resultFuel := hnext.resultFuel
      traceSafe := MovementTraceSafe.bind current next value hcurrent
        hcurrentSafe hnext.traceSafe
      exactErasure := herase
      tempInvariant := hnext.tempInvariant
      tempLive := hnext.tempLive
      requestFits := hnext.requestFits
      valuesMode := hnext.valuesMode
      stableFrame := hnext.stableFrame
      storageFrame := hnext.storageFrame }

theorem mergeHiGallopBTraced_safe
    (origin : MergeState κ ν) (request fuel : Nat)
    (afterB : MergeHiCursor κ ν) (aCount : Nat)
    (hinvariant : MergeHiCursorInvariant origin request afterB)
    (hfuel : MergeHiFuelInvariant fuel afterB)
    (hna : 0 < afterB.na) (hnb : 1 < afterB.nb)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : MergeHiContinuationSafe origin request fuel nextTraced next) :
    ∃ result, MergeHiCorePost origin request
      (mergeHiGallopBTraced? afterB aCount nextTraced)
      (mergeHiGallopB? afterB aCount next) result := by
  have hssa := hinvariant.ssaInBounds hna
  rcases SortSlice.read_eq_some_of_indexInBounds afterB.state.data afterB.ssa
      hssa with ⟨left, hleft⟩
  have hleftResult :
      (TraceResult.sortSliceKeysRead? afterB.state.data afterB.ssa).result =
        some left := by
    change (TraceResult.sortSliceKeysRead? afterB.state.data afterB.ssa).erase =
      some left
    simpa using hleft
  have hleftSafe := mergeHiMainKeyReadTraced_safe afterB.state.data afterB.ssa
    hssa
  have hprefixInitialized : MergeHiTempPrefixInitialized afterB.state.a
      afterB.nb := by
    intro offset hoffset
    rcases hinvariant.tempValuesMode offset hoffset with
      ⟨entry, hread, _hmode⟩
    rw [erase_mergeTempRead] at hread
    refine ⟨entry, ?_⟩
    simpa [mergeTempRead_eq_mergeHiTempRead] using hread
  rcases mergeHiInitializedTempPrefix_exists_of_initialized afterB.state.a
      afterB.nb hprefixInitialized with ⟨temp, htemp⟩
  have htempResult :
      (mergeHiTraceOption (initializedTempPrefix? afterB.state.a
        afterB.nb)).result = some temp := by
    rw [htemp]
    rfl
  have htempSafe : MovementTraceSafe
      (mergeHiTraceOption (initializedTempPrefix? afterB.state.a
        afterB.nb)) := by
    simpa [mergeHiTraceOption, htemp] using MovementTraceSafe.pure temp
  have hagrees := initializedTempPrefix_agreesWithSlice_of_eq_some
    afterB.state.a afterB.nb temp htemp
  rcases gallopLeft_temporary_safe afterB.state afterB.state.a 0 temp 0
      left.key afterB.nb (afterB.nb - 1) hinvariant.temporaryValidRange
      hinvariant.tempLive hagrees (by omega) (by omega)
      hinvariant.rightWordBound with
    ⟨gallopB, hgallop, hgallopFuel, hgallopBound, htraceFuel,
      htracePushes, htraceBounds, htraceLive, hgallopErase⟩
  have hgallopSafe : MovementTraceSafe
      (gallopLeftTraced? afterB.state (.temporary afterB.state.a 0)
        left.key afterB.nb (afterB.nb - 1)) :=
    ⟨htraceFuel, htracePushes, htraceBounds, htraceLive⟩
  rcases mergeHiGallopBAfterTraced_safe origin request fuel afterB aCount
      gallopB hinvariant hfuel hna hgallopBound hgallopFuel nextTraced next
      hnext with ⟨result, hafter⟩
  have hgallopPost := MergeHiCorePost.prepend origin request
    (gallopLeftTraced? afterB.state (.temporary afterB.state.a 0)
      left.key afterB.nb (afterB.nb - 1))
    (fun gallop => mergeHiGallopBAfterTraced? afterB aCount gallop
      nextTraced)
    (fun gallop => mergeHiGallopBAfter? afterB aCount gallop next)
    gallopB result hgallop hgallopSafe hafter
  have hgallopPost' : MergeHiCorePost origin request
      ((gallopLeftTraced? afterB.state (.temporary afterB.state.a 0)
        left.key afterB.nb (afterB.nb - 1)).bind fun gallop =>
          mergeHiGallopBAfterTraced? afterB aCount gallop nextTraced)
      (mergeHiBindOptionAcross
        (gallopLeft? afterB.state temp 0 left.key afterB.nb
          (afterB.nb - 1))
        (fun gallop => mergeHiGallopBAfter? afterB aCount gallop next))
      result := by
    apply hgallopPost.reference_eq
    rw [hgallopErase]
    unfold mergeHiBindOptionAcross
    cases gallopLeft? afterB.state temp 0 left.key afterB.nb
      (afterB.nb - 1) <;> rfl
  have htempPost := MergeHiCorePost.prepend origin request
    (mergeHiTraceOption (initializedTempPrefix? afterB.state.a afterB.nb))
    (fun _temp =>
      (gallopLeftTraced? afterB.state (.temporary afterB.state.a 0)
        left.key afterB.nb (afterB.nb - 1)).bind fun gallop =>
          mergeHiGallopBAfterTraced? afterB aCount gallop nextTraced)
    (fun materialized => mergeHiBindOptionAcross
      (gallopLeft? afterB.state materialized 0 left.key afterB.nb
        (afterB.nb - 1))
      (fun gallop => mergeHiGallopBAfter? afterB aCount gallop next))
    temp result htempResult htempSafe hgallopPost'
  have htempPost' : MergeHiCorePost origin request
      ((mergeHiTraceOption
        (initializedTempPrefix? afterB.state.a afterB.nb)).bind fun _temp =>
          (gallopLeftTraced? afterB.state (.temporary afterB.state.a 0)
            left.key afterB.nb (afterB.nb - 1)).bind fun gallop =>
              mergeHiGallopBAfterTraced? afterB aCount gallop nextTraced)
      ((initializedTempPrefix? afterB.state.a afterB.nb).bind fun materialized =>
        mergeHiBindOptionAcross
          (gallopLeft? afterB.state materialized 0 left.key afterB.nb
            (afterB.nb - 1))
          (fun gallop => mergeHiGallopBAfter? afterB aCount gallop next))
      result := by
    apply htempPost.reference_eq
    rw [erase_mergeHiTraceOption]
  have hleftPost := MergeHiCorePost.prepend origin request
    (TraceResult.sortSliceKeysRead? afterB.state.data afterB.ssa)
    (fun read =>
      (mergeHiTraceOption
        (initializedTempPrefix? afterB.state.a afterB.nb)).bind fun _temp =>
          (gallopLeftTraced? afterB.state (.temporary afterB.state.a 0)
            read.key afterB.nb (afterB.nb - 1)).bind fun gallop =>
              mergeHiGallopBAfterTraced? afterB aCount gallop nextTraced)
    (fun read =>
      (initializedTempPrefix? afterB.state.a afterB.nb).bind fun materialized =>
        mergeHiBindOptionAcross
          (gallopLeft? afterB.state materialized 0 read.key afterB.nb
            (afterB.nb - 1))
          (fun gallop => mergeHiGallopBAfter? afterB aCount gallop next))
    left result hleftResult hleftSafe htempPost'
  have hleftPost' := hleftPost.reference_eq
    (mergeHiGallopB_eq_helpers afterB aCount next).symm
  exact ⟨result, by
    simpa only [mergeHiGallopBTraced?, TraceResult.erase_sortSliceKeysRead]
      using hleftPost'⟩

theorem mergeHiGallopRoundFinishTraced_safe
    (origin : MergeState κ ν) (request fuel : Nat)
    (movedA : MergeHiCursor κ ν) (aCount : Nat)
    (hinvariant : MergeHiCursorInvariant origin request movedA)
    (hbudget : movedA.na + movedA.nb ≤ fuel)
    (hterminalFuel : movedA.na = 0 → MergeHiFuelInvariant fuel movedA)
    (hnb : 1 < movedA.nb)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : MergeHiContinuationSafe origin request fuel nextTraced next) :
    ∃ result, MergeHiCorePost origin request
      (mergeHiGallopRoundFinishTraced? movedA aCount nextTraced)
      (mergeHiGallopRoundFinish? movedA aCount next) result := by
  by_cases hnaZero : movedA.na = 0
  · rcases hnext movedA hinvariant (hterminalFuel hnaZero) with
      ⟨result, hresult⟩
    exact ⟨result, by
      simpa [mergeHiGallopRoundFinishTraced?, mergeHiGallopRoundFinish?,
        hnaZero] using hresult⟩
  · have hna : 0 < movedA.na := Nat.pos_of_ne_zero hnaZero
    rcases mergeHiCopyTempDecrTraced_safe origin request movedA hinvariant
        (by omega) with
      ⟨copiedB, hcopy, hcopySafe, hcopiedInv, _hdst, _hsrc⟩
    let afterB : MergeHiCursor κ ν :=
      { movedA with
        state := copiedB.state
        dest := copiedB.dst
        ssb := copiedB.src
        nb := movedA.nb - 1 }
    have hafterInv : MergeHiCursorInvariant origin request afterB := hcopiedInv
    have hafterFuel : MergeHiFuelInvariant fuel afterB := by
      change movedA.na + (movedA.nb - 1) < fuel
      omega
    let tracedTail := fun copied : MergeHiDataCursorResult κ ν =>
      let cursor : MergeHiCursor κ ν :=
        { movedA with
          state := copied.state
          dest := copied.dst
          ssb := copied.src
          nb := movedA.nb - 1 }
      if cursor.nb = 1 then nextTraced cursor
      else mergeHiGallopBTraced? cursor aCount nextTraced
    let tail := fun copied : MergeHiDataCursorResult κ ν =>
      let cursor : MergeHiCursor κ ν :=
        { movedA with
          state := copied.state
          dest := copied.dst
          ssb := copied.src
          nb := movedA.nb - 1 }
      if cursor.nb = 1 then next cursor
      else mergeHiGallopB? cursor aCount next
    have htail : ∃ result, MergeHiCorePost origin request
        (tracedTail copiedB) (tail copiedB) result := by
      by_cases hone : afterB.nb = 1
      · rcases hnext afterB hafterInv hafterFuel with ⟨result, hresult⟩
        have hone' : movedA.nb - 1 = 1 := by simpa [afterB] using hone
        exact ⟨result, by
          simp only [tracedTail, tail]
          rw [if_pos hone', if_pos hone']
          exact hresult⟩
      · have hafterNa : 0 < afterB.na := by simpa [afterB] using hna
        have hafterNb : 1 < afterB.nb := by
          change 1 < movedA.nb - 1
          have hone' : ¬ movedA.nb - 1 = 1 := by
            simpa [afterB] using hone
          omega
        rcases mergeHiGallopBTraced_safe origin request fuel afterB aCount
            hafterInv hafterFuel hafterNa hafterNb nextTraced next hnext with
          ⟨result, hresult⟩
        have hone' : ¬ movedA.nb - 1 = 1 := by simpa [afterB] using hone
        exact ⟨result, by
          simp only [tracedTail, tail]
          rw [if_neg hone', if_neg hone']
          exact hresult⟩
    rcases htail with ⟨result, htail⟩
    have hpost := MergeHiCorePost.prepend origin request
      (mergeHiCopyTempDecrTraced? movedA.state movedA.dest movedA.ssb)
      tracedTail tail copiedB result hcopy hcopySafe htail
    exact ⟨result, by
      simpa [mergeHiGallopRoundFinishTraced?, mergeHiGallopRoundFinish?,
        hnaZero, tracedTail, tail] using hpost⟩

theorem mergeHiGallopRoundAfterTraced_safe
    (origin : MergeState κ ν) (request fuel : Nat)
    (cursor : MergeHiCursor κ ν) (minGallop : PySSize)
    (state : MergeState κ ν) (gallopA : GallopResult)
    (hinvariant : MergeHiCursorInvariant origin request
      { cursor with state := state, minGallop := minGallop })
    (hfuel : MergeHiFuelInvariant (fuel + 1) cursor)
    (hna : 0 < cursor.na) (hnb : 1 < cursor.nb)
    (hbound : gallopA.index ≤ cursor.na)
    (hnotFuel : gallopA.fuelExhausted = false)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : MergeHiContinuationSafe origin request fuel nextTraced next) :
    ∃ result, MergeHiCorePost origin request
      (mergeHiGallopRoundAfterTraced? cursor minGallop state gallopA nextTraced)
      (mergeHiGallopRoundAfter? cursor minGallop state gallopA next) result := by
  let adjusted : MergeHiCursor κ ν :=
    { cursor with state := state, minGallop := minGallop }
  let aCount := cursor.na - gallopA.index
  have haCount : aCount ≤ adjusted.na := by
    simp [aCount, adjusted]
  rcases mergeHiMoveABlockTraced_safe origin request adjusted hinvariant
      aCount haCount with
    ⟨movedA, hmove, hmoveSafe, hmovedInv, hmovedNa, hmovedNb⟩
  have hmovedBudget : movedA.na + movedA.nb ≤ fuel := by
    have hf := hfuel
    change cursor.na + cursor.nb < fuel + 1 at hf
    rw [hmovedNa, hmovedNb]
    simp only [adjusted]
    omega
  have hmovedTerminalFuel : movedA.na = 0 →
      MergeHiFuelInvariant fuel movedA := by
    intro hmovedZero
    have hf := hfuel
    change cursor.na + cursor.nb < fuel + 1 at hf
    change movedA.na + movedA.nb < fuel
    rw [hmovedNa, hmovedNb]
    have hmovedZero' : adjusted.na - aCount = 0 := by
      rw [← hmovedNa]
      exact hmovedZero
    have hcursorZero : cursor.na - aCount = 0 := by
      simpa [adjusted] using hmovedZero'
    simp only [adjusted]
    have haPositive : 0 < aCount := by
      omega
    omega
  have hmovedNbPositive : 1 < movedA.nb := by
    simpa [hmovedNb, adjusted] using hnb
  rcases mergeHiGallopRoundFinishTraced_safe origin request fuel movedA aCount
      hmovedInv hmovedBudget hmovedTerminalFuel hmovedNbPositive nextTraced next
      hnext with ⟨result, hfinish⟩
  have hpost := MergeHiCorePost.prepend origin request
    (mergeHiMoveABlockTraced? adjusted aCount)
    (fun moved => mergeHiGallopRoundFinishTraced? moved aCount nextTraced)
    (fun moved => mergeHiGallopRoundFinish? moved aCount next)
    movedA result hmove hmoveSafe hfinish
  exact ⟨result, by
    simpa [mergeHiGallopRoundAfterTraced?, mergeHiGallopRoundAfter?,
      hnotFuel, adjusted, aCount] using hpost⟩

theorem mergeHiGallopRoundTraced_safe
    (origin : MergeState κ ν) (request fuel : Nat)
    (cursor : MergeHiCursor κ ν)
    (hinvariant : MergeHiCursorInvariant origin request cursor)
    (hfuel : MergeHiFuelInvariant (fuel + 1) cursor)
    (hna : 0 < cursor.na) (hnb : 1 < cursor.nb)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : MergeHiContinuationSafe origin request fuel nextTraced next) :
    ∃ result, MergeHiCorePost origin request
      (mergeHiGallopRoundTraced? cursor nextTraced)
      (mergeHiGallopRound? cursor next) result := by
  let minGallop := mergeHiDecreaseMinGallop cursor.minGallop
  let state : MergeState κ ν := { cursor.state with min_gallop := minGallop }
  let adjusted : MergeHiCursor κ ν :=
    { cursor with state := state, minGallop := minGallop }
  have hadjustedInv : MergeHiCursorInvariant origin request adjusted := by
    exact hinvariant.setMinGallop minGallop
  have hnbPositive : 0 < adjusted.nb := by
    simpa [adjusted] using Nat.zero_lt_of_lt hnb
  rcases hadjustedInv.tempReadable hnbPositive with ⟨right, hright⟩
  have hrightResult :
      (TraceResult.tempPayloadRead? state.a cursor.ssb).result = some right := by
    change (TraceResult.tempPayloadRead? state.a cursor.ssb).erase = some right
    rw [erase_mergeTempRead]
    simpa [adjusted, state] using hright
  have hrightSafe : MovementTraceSafe
      (TraceResult.tempPayloadRead? state.a cursor.ssb) := by
    apply mergeHiTempReadTraced_safe
    · simpa [adjusted, state] using hadjustedInv.ssbInBounds hnbPositive
    · simpa [adjusted, state] using hadjustedInv.tempLive
  have hvalid :
      (GallopKeySource.main state.data cursor.basea).ValidRange cursor.na := by
    simpa [adjusted, state] using hadjustedInv.mainValidRange
  rcases gallopRight_main_safe state state.data cursor.basea right.key
      cursor.na (cursor.na - 1) hvalid hna (by omega)
      hinvariant.leftWordBound with
    ⟨gallopA, hgallopResult, hgallopFuel, hgallopBound,
      hgallopTraceFuel, hgallopNoPushes, hgallopBounds, hgallopLive,
      hgallopErase⟩
  have hgallopSafe : MovementTraceSafe
      (gallopRightTraced? state (.main state.data cursor.basea) right.key
        cursor.na (cursor.na - 1)) :=
    ⟨hgallopTraceFuel, hgallopNoPushes, hgallopBounds, hgallopLive⟩
  rcases mergeHiGallopRoundAfterTraced_safe origin request fuel cursor
      minGallop state gallopA hadjustedInv hfuel hna hnb hgallopBound
      hgallopFuel nextTraced next hnext with ⟨result, hafter⟩
  have hgallopPost := MergeHiCorePost.prepend origin request
    (gallopRightTraced? state (.main state.data cursor.basea) right.key
      cursor.na (cursor.na - 1))
    (fun gallop =>
      mergeHiGallopRoundAfterTraced? cursor minGallop state gallop nextTraced)
    (fun gallop =>
      mergeHiGallopRoundAfter? cursor minGallop state gallop next)
    gallopA result hgallopResult hgallopSafe hafter
  have hgallopPost' : MergeHiCorePost origin request
      ((gallopRightTraced? state (.main state.data cursor.basea) right.key
        cursor.na (cursor.na - 1)).bind fun gallop =>
          mergeHiGallopRoundAfterTraced? cursor minGallop state gallop
            nextTraced)
      (mergeHiBindOptionAcross
        (gallopRight? state state.data cursor.basea right.key cursor.na
          (cursor.na - 1))
        (fun gallop =>
          mergeHiGallopRoundAfter? cursor minGallop state gallop next))
      result := by
    apply hgallopPost.reference_eq
    rw [hgallopErase]
    unfold mergeHiBindOptionAcross
    cases gallopRight? state state.data cursor.basea right.key cursor.na
      (cursor.na - 1) <;> rfl
  have hrightPost := MergeHiCorePost.prepend origin request
    (TraceResult.tempPayloadRead? state.a cursor.ssb)
    (fun entry =>
      (gallopRightTraced? state (.main state.data cursor.basea) entry.key
        cursor.na (cursor.na - 1)).bind fun gallop =>
          mergeHiGallopRoundAfterTraced? cursor minGallop state gallop
            nextTraced)
    (fun entry =>
      mergeHiBindOptionAcross
        (gallopRight? state state.data cursor.basea entry.key cursor.na
          (cursor.na - 1))
        (fun gallop =>
          mergeHiGallopRoundAfter? cursor minGallop state gallop next))
    right result hrightResult hrightSafe hgallopPost'
  have hrightPost' : MergeHiCorePost origin request
      ((TraceResult.tempPayloadRead? state.a cursor.ssb).bind fun entry =>
        (gallopRightTraced? state (.main state.data cursor.basea) entry.key
          cursor.na (cursor.na - 1)).bind fun gallop =>
            mergeHiGallopRoundAfterTraced? cursor minGallop state gallop
              nextTraced)
      ((mergeTempRead? state.a cursor.ssb).bind fun entry =>
        mergeHiBindOptionAcross
          (gallopRight? state state.data cursor.basea entry.key cursor.na
            (cursor.na - 1))
          (fun gallop =>
            mergeHiGallopRoundAfter? cursor minGallop state gallop next))
      result := by
    apply hrightPost.reference_eq
    rw [erase_mergeTempRead]
  have hrightPost'' := hrightPost'.reference_eq
    (by simpa [minGallop, state] using
      (mergeHiGallopRound_eq_helpers cursor next).symm)
  exact ⟨result, by
    simpa only [mergeHiGallopRoundTraced?] using hrightPost''⟩

/-- Complete recursive driver contract.  The strict slack is consumed by one
real backward copy before each recursive call, while both terminal labels are
handled before phase dispatch. -/
theorem mergeHiLoopTraced_safe
    (origin : MergeState κ ν) (request fuel : Nat)
    (cursor : MergeHiCursor κ ν)
    (hinvariant : MergeHiCursorInvariant origin request cursor)
    (hfuel : MergeHiFuelInvariant fuel cursor) :
    ∃ result, MergeHiCorePost origin request
      (mergeHiLoopTraced? fuel cursor) (mergeHiLoop? fuel cursor) result := by
  induction fuel generalizing cursor with
  | zero =>
      unfold MergeHiFuelInvariant at hfuel
      omega
  | succ fuel ih =>
      by_cases hterminal : cursor.na = 0 ∨ cursor.nb = 0
      · simpa [mergeHiLoopTraced?, mergeHiLoop?, hterminal] using
          mergeHiSucceedTraced_safe origin request cursor hinvariant
      · have hna : 0 < cursor.na := by omega
        have hnbPositive : 0 < cursor.nb := by omega
        by_cases hnbOne : cursor.nb = 1
        · have hnaZero : ¬ cursor.na = 0 := by omega
          simpa [mergeHiLoopTraced?, mergeHiLoop?, hterminal, hnbOne,
            hnaZero] using
            mergeHiCopyATraced_safe origin request cursor hinvariant
              ⟨hnbOne, hna⟩
        · have hnb : 1 < cursor.nb := by omega
          cases hphase : cursor.phase with
          | galloping aCount bCount =>
              simpa [mergeHiLoopTraced?, mergeHiLoop?, hterminal, hnbOne,
                hphase] using
                mergeHiGallopRoundTraced_safe origin request fuel cursor
                  hinvariant hfuel hna hnb (mergeHiLoopTraced? fuel)
                  (mergeHiLoop? fuel) ih
          | straight aCount bCount =>
              rcases hinvariant.tempReadable hnbPositive with
                ⟨right, hright⟩
              have hrightResult :
                  (TraceResult.tempPayloadRead? cursor.state.a
                    cursor.ssb).result = some right := by
                change (TraceResult.tempPayloadRead? cursor.state.a
                  cursor.ssb).erase = some right
                rw [erase_mergeTempRead]
                exact hright
              have hrightSafe := mergeHiTempReadTraced_safe cursor.state.a
                cursor.ssb (hinvariant.ssbInBounds hnbPositive)
                hinvariant.tempLive
              rcases SortSlice.read_eq_some_of_indexInBounds cursor.state.data
                  cursor.ssa (hinvariant.ssaInBounds hna) with
                ⟨left, hleft⟩
              have hleftResult :
                  (TraceResult.sortSliceKeysRead? cursor.state.data
                    cursor.ssa).result = some left := by
                change cursor.state.data.read? cursor.ssa = some left
                exact hleft
              have hleftSafe := mergeHiMainKeyReadTraced_safe
                cursor.state.data cursor.ssa (hinvariant.ssaInBounds hna)
              let tracedAfterLeft := fun (rightEntry entry : SortSliceEntry κ ν) =>
                if iflt cursor.state.key_compare rightEntry.key entry.key then
                  (mergeHiCopyDataDecrTraced? cursor.state cursor.dest
                    cursor.ssa).bind fun copied =>
                      let nextCount := aCount + 1
                      let next : MergeHiCursor κ ν :=
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssa := copied.src
                          na := cursor.na - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping nextCount 0
                            else
                              .straight nextCount 0
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else
                              cursor.minGallop }
                      mergeHiLoopTraced? fuel next
                else
                  (mergeHiCopyTempDecrTraced? cursor.state cursor.dest
                    cursor.ssb).bind fun copied =>
                      let nextCount := bCount + 1
                      let next : MergeHiCursor κ ν :=
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssb := copied.src
                          nb := cursor.nb - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping 0 nextCount
                            else
                              .straight 0 nextCount
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else
                              cursor.minGallop }
                      mergeHiLoopTraced? fuel next
              let referenceAfterLeft := fun
                  (rightEntry entry : SortSliceEntry κ ν) =>
                if iflt cursor.state.key_compare rightEntry.key entry.key then
                  (mergeHiCopyDataDecr? cursor.state cursor.dest
                    cursor.ssa).bind fun copied =>
                      let nextCount := aCount + 1
                      let next : MergeHiCursor κ ν :=
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssa := copied.src
                          na := cursor.na - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping nextCount 0
                            else
                              .straight nextCount 0
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else
                              cursor.minGallop }
                      mergeHiLoop? fuel next
                else
                  (mergeHiCopyTempDecr? cursor.state cursor.dest
                    cursor.ssb).bind fun copied =>
                      let nextCount := bCount + 1
                      let next : MergeHiCursor κ ν :=
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssb := copied.src
                          nb := cursor.nb - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping 0 nextCount
                            else
                              .straight 0 nextCount
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else
                              cursor.minGallop }
                      mergeHiLoop? fuel next
              have hselected : ∃ result, MergeHiCorePost origin request
                  (tracedAfterLeft right left)
                  (referenceAfterLeft right left) result := by
                by_cases hcompare :
                    cursor.state.key_compare right.key left.key = true
                · rcases mergeHiCopyDataDecrTraced_safe origin request cursor
                      hinvariant hna with
                    ⟨copied, hcopy, hcopySafe, hcopiedInv, _hdst, _hsrc⟩
                  let nextCount := aCount + 1
                  let next : MergeHiCursor κ ν :=
                    { cursor with
                      state := copied.state
                      dest := copied.dst
                      ssa := copied.src
                      na := cursor.na - 1
                      phase :=
                        if mergeHiCountAtLeast nextCount cursor.minGallop then
                          .galloping nextCount 0
                        else
                          .straight nextCount 0
                      minGallop :=
                        if mergeHiCountAtLeast nextCount cursor.minGallop then
                          cursor.minGallop + 1
                        else
                          cursor.minGallop }
                  have hnextInv : MergeHiCursorInvariant origin request next := by
                    by_cases hcross :
                        mergeHiCountAtLeast nextCount cursor.minGallop = true
                    · simpa [next, nextCount, hcross] using
                        hcopiedInv.setControl (cursor.minGallop + 1)
                          (.galloping nextCount 0)
                    · simpa [next, nextCount, hcross] using
                        hcopiedInv.setControl cursor.minGallop
                          (.straight nextCount 0)
                  have hnextFuel : MergeHiFuelInvariant fuel next := by
                    unfold MergeHiFuelInvariant at hfuel ⊢
                    simp only [next]
                    omega
                  rcases ih next hnextInv hnextFuel with ⟨result, htail⟩
                  have hcopyPost := MergeHiCorePost.prepend origin request
                    (mergeHiCopyDataDecrTraced? cursor.state cursor.dest
                      cursor.ssa)
                    (fun copied =>
                      let nextCount := aCount + 1
                      mergeHiLoopTraced? fuel
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssa := copied.src
                          na := cursor.na - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping nextCount 0
                            else .straight nextCount 0
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else cursor.minGallop })
                    (fun copied =>
                      let nextCount := aCount + 1
                      mergeHiLoop? fuel
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssa := copied.src
                          na := cursor.na - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping nextCount 0
                            else .straight nextCount 0
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else cursor.minGallop })
                    copied result hcopy hcopySafe (by
                      simpa [next, nextCount] using htail)
                  exact ⟨result, by
                    simpa [tracedAfterLeft, referenceAfterLeft, hcompare,
                      erase_mergeHiCopyDataDecrTraced] using hcopyPost⟩
                · rcases mergeHiCopyTempDecrTraced_safe origin request cursor
                      hinvariant hnbPositive with
                    ⟨copied, hcopy, hcopySafe, hcopiedInv, _hdst, _hsrc⟩
                  let nextCount := bCount + 1
                  let next : MergeHiCursor κ ν :=
                    { cursor with
                      state := copied.state
                      dest := copied.dst
                      ssb := copied.src
                      nb := cursor.nb - 1
                      phase :=
                        if mergeHiCountAtLeast nextCount cursor.minGallop then
                          .galloping 0 nextCount
                        else
                          .straight 0 nextCount
                      minGallop :=
                        if mergeHiCountAtLeast nextCount cursor.minGallop then
                          cursor.minGallop + 1
                        else
                          cursor.minGallop }
                  have hnextInv : MergeHiCursorInvariant origin request next := by
                    by_cases hcross :
                        mergeHiCountAtLeast nextCount cursor.minGallop = true
                    · simpa [next, nextCount, hcross] using
                        hcopiedInv.setControl (cursor.minGallop + 1)
                          (.galloping 0 nextCount)
                    · simpa [next, nextCount, hcross] using
                        hcopiedInv.setControl cursor.minGallop
                          (.straight 0 nextCount)
                  have hnextFuel : MergeHiFuelInvariant fuel next := by
                    unfold MergeHiFuelInvariant at hfuel ⊢
                    simp only [next]
                    omega
                  rcases ih next hnextInv hnextFuel with ⟨result, htail⟩
                  have hcopyPost := MergeHiCorePost.prepend origin request
                    (mergeHiCopyTempDecrTraced? cursor.state cursor.dest
                      cursor.ssb)
                    (fun copied =>
                      let nextCount := bCount + 1
                      mergeHiLoopTraced? fuel
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssb := copied.src
                          nb := cursor.nb - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping 0 nextCount
                            else .straight 0 nextCount
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else cursor.minGallop })
                    (fun copied =>
                      let nextCount := bCount + 1
                      mergeHiLoop? fuel
                        { cursor with
                          state := copied.state
                          dest := copied.dst
                          ssb := copied.src
                          nb := cursor.nb - 1
                          phase :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              .galloping 0 nextCount
                            else .straight 0 nextCount
                          minGallop :=
                            if mergeHiCountAtLeast nextCount cursor.minGallop then
                              cursor.minGallop + 1
                            else cursor.minGallop })
                    copied result hcopy hcopySafe (by
                      simpa [next, nextCount] using htail)
                  exact ⟨result, by
                    simpa [tracedAfterLeft, referenceAfterLeft, hcompare,
                      erase_mergeHiCopyTempDecrTraced] using hcopyPost⟩
              rcases hselected with ⟨result, hselected⟩
              have hleftPost := MergeHiCorePost.prepend origin request
                (TraceResult.sortSliceKeysRead? cursor.state.data cursor.ssa)
                (tracedAfterLeft right) (referenceAfterLeft right) left result
                hleftResult
                hleftSafe hselected
              let tracedAfterRight := fun (entry : SortSliceEntry κ ν) =>
                (TraceResult.sortSliceKeysRead? cursor.state.data
                  cursor.ssa).bind (tracedAfterLeft entry)
              let referenceAfterRight := fun (entry : SortSliceEntry κ ν) =>
                cursor.state.data.read? cursor.ssa |>.bind
                  (referenceAfterLeft entry)
              have hleftPost' : MergeHiCorePost origin request
                  (tracedAfterRight right) (referenceAfterRight right) result := by
                simpa [tracedAfterRight, referenceAfterRight] using hleftPost
              have hrightPost := MergeHiCorePost.prepend origin request
                (TraceResult.tempPayloadRead? cursor.state.a cursor.ssb)
                tracedAfterRight referenceAfterRight right result hrightResult
                hrightSafe hleftPost'
              have hrightPost' : MergeHiCorePost origin request
                  ((TraceResult.tempPayloadRead? cursor.state.a
                    cursor.ssb).bind tracedAfterRight)
                  ((mergeTempRead? cursor.state.a cursor.ssb).bind
                    referenceAfterRight) result := by
                apply hrightPost.reference_eq
                rw [erase_mergeTempRead]
              exact ⟨result, by
                simpa [mergeHiLoopTraced?, mergeHiLoop?, hterminal, hnbOne,
                  hphase, tracedAfterRight, referenceAfterRight,
                  tracedAfterLeft, referenceAfterLeft,
                  mergeTempRead_eq_mergeHiTempRead]
                  using hrightPost'⟩

end MergeHiCursorInvariant
end MergeHiStorageFrame
end MergeHiStableFrame
end CPythonListsort

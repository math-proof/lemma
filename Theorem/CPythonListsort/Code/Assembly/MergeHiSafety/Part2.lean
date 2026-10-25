/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeHiSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.MergeTracePrimitives.Part5
import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety
import Def.CPythonListsort.Code.Assembly.MergeHiSafety
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

@[simp]
theorem erase_mergeHiGallopBAfterTraced
    (afterB : MergeHiCursor κ ν) (aCount : Nat) (gallopB : GallopResult)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : ∀ cursor, (nextTraced cursor).erase = next cursor) :
    (mergeHiGallopBAfterTraced? afterB aCount gallopB nextTraced).erase =
      mergeHiGallopBAfter? afterB aCount gallopB next := by
  unfold mergeHiGallopBAfterTraced? mergeHiGallopBAfter?
  cases hfuel : gallopB.fuelExhausted with
  | false =>
    change
      ((mergeHiMoveBBlockTraced? afterB
        (afterB.nb - gallopB.index)).bind fun movedB =>
          mergeHiGallopBFinishTraced? afterB aCount
            (afterB.nb - gallopB.index) movedB nextTraced).erase =
      (mergeHiMoveBBlock? afterB (afterB.nb - gallopB.index)).bind
        fun movedB => mergeHiGallopBFinish? afterB aCount
          (afterB.nb - gallopB.index) movedB next
    rw [TraceResult.erase_bind, erase_mergeHiMoveBBlockTraced]
    apply Option.bind_congr
    intro movedB _hmoved
    exact erase_mergeHiGallopBFinishTraced afterB aCount
      (afterB.nb - gallopB.index) movedB nextTraced next hnext
  | true =>
    change (mergeHiFuelExhaustedTraced afterB).erase =
      some (mergeHiFuelExhausted afterB)
    simp [mergeHiFuelExhaustedTraced]

theorem mergeHiGallopB_eq_helpers
    (afterB : MergeHiCursor κ ν) (aCount : Nat)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) :
    mergeHiGallopB? afterB aCount next =
      (afterB.state.data.read? afterB.ssa).bind fun left =>
        (initializedTempPrefix? afterB.state.a afterB.nb).bind fun temp =>
          mergeHiBindOptionAcross
              (gallopLeft? afterB.state temp 0 left.key afterB.nb
                (afterB.nb - 1))
              (fun gallop => mergeHiGallopBAfter? afterB aCount gallop next) := by
  unfold mergeHiGallopB? mergeHiGallopBAfter?
  cases hleft : afterB.state.data.read? afterB.ssa with
  | none => simp [bind, Option.bind]
  | some left =>
    simp only [bind, Option.bind]
    cases htemp : initializedTempPrefix? afterB.state.a afterB.nb with
    | none => simp
    | some temp =>
      simp only [Bool.or_eq_true, BitVec.ofNat_eq_ofNat,
        Int.ofNat_eq_natCast]
      cases hgallop : gallopLeft? afterB.state temp 0 left.key afterB.nb
          (afterB.nb - 1) with
      | none => simp [mergeHiBindOptionAcross]
      | some gallop =>
        simp only [mergeHiBindOptionAcross]
        cases hfuel : gallop.fuelExhausted with
        | true =>
          have htrue : (true : Bool) = true := rfl
          rw [if_pos htrue, if_pos htrue]
        | false =>
          have hfalse : ¬ (false : Bool) = true := by decide
          rw [if_neg hfalse, if_neg hfalse]
          by_cases hcount : afterB.nb - gallop.index = 0
          · simp [Option.bind, hcount, mergeHiMoveBBlock?,
              mergeHiGallopBFinish?]
          · simp only [hcount, ↓reduceIte, mergeHiMoveBBlock?]
            cases hcopy : mergeHiMemcpyTempToData? .gallopTempToData rfl
                (afterB.nb - gallop.index) afterB.state
                (afterB.dest - Int.ofNat (afterB.nb - gallop.index) + 1)
                (afterB.ssb - Int.ofNat (afterB.nb - gallop.index) + 1) <;>
              simp [bind, Option.bind, mergeHiGallopBFinish?]

theorem mergeHiGallopRound_eq_helpers
    (cursor : MergeHiCursor κ ν)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) :
    mergeHiGallopRound? cursor next =
      let minGallop := mergeHiDecreaseMinGallop cursor.minGallop
      let state := { cursor.state with min_gallop := minGallop }
      (mergeTempRead? state.a cursor.ssb).bind fun right =>
        mergeHiBindOptionAcross
          (gallopRight? state state.data cursor.basea right.key
            cursor.na (cursor.na - 1))
          (fun gallopA =>
            mergeHiGallopRoundAfter? cursor minGallop state gallopA next) := by
  simp only [mergeHiGallopRound?, mergeDataMemmove_eq,
    mergeTempRead_eq_mergeHiTempRead]
  cases hright : mergeHiTempRead?
      { cursor.state with
        min_gallop := mergeHiDecreaseMinGallop cursor.minGallop }.a
      cursor.ssb with
  | none => simp [bind, Option.bind]
  | some right =>
      simp only [bind, Option.bind]
      cases hgallop : gallopRight?
          { cursor.state with
            min_gallop := mergeHiDecreaseMinGallop cursor.minGallop }
          { cursor.state with
            min_gallop := mergeHiDecreaseMinGallop cursor.minGallop }.data
          cursor.basea right.key cursor.na (cursor.na - 1) with
      | none => simp [mergeHiBindOptionAcross]
      | some gallop =>
          simp only [mergeHiBindOptionAcross]
          cases hfuel : gallop.fuelExhausted with
          | true => simp [mergeHiGallopRoundAfter?, hfuel]
          | false =>
              simp only [mergeHiGallopRoundAfter?, hfuel, Bool.false_eq_true,
                ↓reduceIte]
              by_cases hcount : cursor.na - gallop.index = 0
              · simp only [mergeHiMoveABlock?, hcount, ↓reduceIte,
                  mergeHiGallopRoundFinish?]
                rfl
              · simp only [mergeHiMoveABlock?, hcount, ↓reduceIte]
                cases hmove : cursor.state.data.memmove?
                    (cursor.dest - Int.ofNat (cursor.na - gallop.index) + 1)
                    (cursor.ssa - Int.ofNat (cursor.na - gallop.index) + 1)
                    (cursor.na - gallop.index) with
                | none =>
                    unfold mainDataMemmove?
                    rw [hmove]
                    rfl
                | some data =>
                    unfold mainDataMemmove?
                    rw [hmove]
                    rfl

/-- Erasure commutes with the second half of one `merge_hi` galloping round
whenever it commutes with the supplied continuation. -/
theorem erase_mergeHiGallopBTraced
    (afterB : MergeHiCursor κ ν) (aCount : Nat)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hNext : ∀ cursor, (nextTraced cursor).erase = next cursor) :
    (mergeHiGallopBTraced? afterB aCount nextTraced).erase =
      mergeHiGallopB? afterB aCount next := by
  rw [mergeHiGallopB_eq_helpers]
  unfold mergeHiGallopBTraced?
  rw [TraceResult.erase_bind, TraceResult.erase_sortSliceKeysRead]
  cases hLeft : afterB.state.data.read? afterB.ssa with
  | none => simp
  | some left =>
      simp only [Option.bind_some, TraceResult.erase_bind,
        erase_mergeHiTraceOption]
      cases hTemp : initializedTempPrefix? afterB.state.a afterB.nb with
      | none => simp
      | some temp =>
          simp only [Option.bind_some]
          rw [erase_mergeHiTemporaryGallopLeft_of_eq_some afterB.state
            afterB.nb (afterB.nb - 1) temp left.key hTemp]
          unfold mergeHiBindOptionAcross
          cases hGallop : gallopLeft? afterB.state temp 0 left.key afterB.nb
              (afterB.nb - 1) with
          | none => simp
          | some gallop =>
              simp only [Option.bind_some]
              exact erase_mergeHiGallopBAfterTraced afterB aCount gallop
                nextTraced next hNext

theorem erase_mergeHiGallopRoundFinishTraced
    (movedA : MergeHiCursor κ ν) (aCount : Nat)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hNext : ∀ cursor, (nextTraced cursor).erase = next cursor) :
    (mergeHiGallopRoundFinishTraced? movedA aCount nextTraced).erase =
      mergeHiGallopRoundFinish? movedA aCount next := by
  unfold mergeHiGallopRoundFinishTraced? mergeHiGallopRoundFinish?
  by_cases hFinished : movedA.na = 0
  · simp [hFinished, hNext]
  · rw [if_neg hFinished, if_neg hFinished, TraceResult.erase_bind,
      erase_mergeHiCopyTempDecrTraced]
    apply Option.bind_congr
    intro copiedB _hCopied
    let afterB : MergeHiCursor κ ν :=
      { movedA with
        state := copiedB.state
        dest := copiedB.dst
        ssb := copiedB.src
        nb := movedA.nb - 1 }
    change
      (if afterB.nb = 1 then nextTraced afterB
        else mergeHiGallopBTraced? afterB aCount nextTraced).erase =
      if afterB.nb = 1 then next afterB
        else mergeHiGallopB? afterB aCount next
    by_cases hOne : afterB.nb = 1
    · rw [if_pos hOne, if_pos hOne]
      exact hNext _
    · rw [if_neg hOne, if_neg hOne]
      exact erase_mergeHiGallopBTraced _ _ nextTraced next hNext

theorem erase_mergeHiGallopRoundAfterTraced
    (cursor : MergeHiCursor κ ν) (minGallop : PySSize)
    (state : MergeState κ ν) (gallopA : GallopResult)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hNext : ∀ cursor, (nextTraced cursor).erase = next cursor) :
    (mergeHiGallopRoundAfterTraced? cursor minGallop state gallopA
      nextTraced).erase =
      mergeHiGallopRoundAfter? cursor minGallop state gallopA next := by
  unfold mergeHiGallopRoundAfterTraced? mergeHiGallopRoundAfter?
  cases hFuel : gallopA.fuelExhausted with
  | true => simp [erase_mergeHiFuelExhaustedTraced]
  | false =>
      simp only [Bool.false_eq_true, if_false, TraceResult.erase_bind,
        erase_mergeHiMoveABlockTraced]
      apply Option.bind_congr
      intro movedA _hMoved
      exact erase_mergeHiGallopRoundFinishTraced movedA
        (cursor.na - gallopA.index) nextTraced next hNext

/-- Erasure commutes with one complete `merge_hi` galloping round whenever it
commutes with the supplied continuation.  This premise-free structural bridge
is the proof-only API consumed by the top-level raw-domain erasure chain. -/
theorem erase_mergeHiGallopRoundTraced
    (cursor : MergeHiCursor κ ν)
    (nextTraced : MergeHiCursor κ ν → TraceResult (MergeHiResult κ ν))
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hNext : ∀ cursor, (nextTraced cursor).erase = next cursor) :
    (mergeHiGallopRoundTraced? cursor nextTraced).erase =
      mergeHiGallopRound? cursor next := by
  rw [mergeHiGallopRound_eq_helpers]
  unfold mergeHiGallopRoundTraced?
  let minGallop := mergeHiDecreaseMinGallop cursor.minGallop
  let state : MergeState κ ν := { cursor.state with min_gallop := minGallop }
  change
    ((TraceResult.tempPayloadRead? state.a cursor.ssb).bind fun right =>
      (gallopRightTraced? state (.main state.data cursor.basea) right.key
        cursor.na (cursor.na - 1)).bind fun gallopA =>
          mergeHiGallopRoundAfterTraced? cursor minGallop state gallopA
            nextTraced).erase =
      (mergeTempRead? state.a cursor.ssb).bind fun right =>
        mergeHiBindOptionAcross
          (gallopRight? state state.data cursor.basea right.key cursor.na
            (cursor.na - 1)) fun gallopA =>
              mergeHiGallopRoundAfter? cursor minGallop state gallopA next
  rw [TraceResult.erase_bind, erase_mergeTempRead]
  cases hRight : mergeTempRead? state.a cursor.ssb with
  | none => simp
  | some right =>
      simp only [Option.bind_some, TraceResult.erase_bind]
      rw [erase_gallopRightTraced_main]
      unfold mergeHiBindOptionAcross
      cases hGallop : gallopRight? state state.data cursor.basea right.key
          cursor.na (cursor.na - 1) with
      | none => simp
      | some gallop =>
          simp only [Option.bind_some]
          exact erase_mergeHiGallopRoundAfterTraced cursor minGallop state
            gallop nextTraced next hNext

end CPythonListsort

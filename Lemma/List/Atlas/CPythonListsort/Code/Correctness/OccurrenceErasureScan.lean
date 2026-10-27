import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.CPythonListsort.Code.Correctness.OccurrenceErasureScan.Part2
open CPythonListsort


namespace CPythonListsort

/--
[eraseOccurrenceSetTopPower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
lemma eraseOccurrenceSetTopPower
  {alpha : Type u}
  {nu : Type v}
  {power : Nat}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  setTopPower? (eraseOccurrenceMergeState state) power = (setTopPower? state power).map eraseOccurrenceMergeState := by
-- proof
  simp only [eraseOccurrenceMergeState]
  unfold setTopPower?
  by_cases hempty : state.pending.isEmpty
  · simp [hempty]
  · rw [if_neg hempty, if_neg hempty]
    cases htop : state.pending[state.pending.size - 1]? with
    | none => simp [htop]
    | some top => simp [htop, eraseOccurrenceMergeState]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceForceCollapseIndex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
lemma eraseOccurrenceForceCollapseIndex
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  forceCollapseIndex? (eraseOccurrenceMergeState state) = forceCollapseIndex? state := by
-- proof
  simp [forceCollapseIndex?, eraseOccurrenceMergeState]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrencePrepareMergeAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
lemma eraseOccurrencePrepareMergeAt
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {state : MergeState (Occurrence alpha) nu}
  {i : Nat}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  prepareMergeAt? (eraseOccurrenceMergeState state) i = (prepareMergeAt? state i).map eraseOccurrenceMergeAtPreparation := by
-- proof
  simp only [eraseOccurrenceMergeState]
  unfold prepareMergeAt?
  by_cases hposition :
    2 ≤ state.pending.size ∧
      (i + 2 = state.pending.size ∨ i + 3 = state.pending.size)
  · rw [if_pos hposition, if_pos hposition]
    cases hleft : state.pending[i]? with
    | none => simp
    | some left =>
      simp only [mergeAt_bindOptionAcross_some]
      cases hright : state.pending[i + 1]? with
      | none => simp
      | some right =>
        simp only [mergeAt_bindOptionAcross_some]
        by_cases hgeometry :
          (0 : PySSize).slt left.len ∧
            (0 : PySSize).slt right.len ∧
            left.base + left.len.toNat = right.base
        · rw [if_pos hgeometry, if_pos hgeometry]
          simp only [combinePendingAt_eq]
          let call : MergeState (Occurrence alpha) nu :=
            { state with
              pending :=
                (state.pending.setIfInBounds i
                  { left with len := left.len + right.len }).eraseIdxIfInBounds
                    (i + 1) }
          have heraseCall :
            { eraseOccurrenceMergeState state with
              pending :=
                (state.pending.setIfInBounds i
                  { left with len := left.len + right.len }).eraseIdxIfInBounds
                    (i + 1) } = eraseOccurrenceMergeState call := rfl
          have heraseCall' := heraseCall
          simp only [eraseOccurrenceMergeState] at heraseCall'
          rw [heraseCall']
          have hcallCompare :
            call.key_compare = occurrenceComparator lt := hcompare
          have hcallData : call.data = state.data := rfl
          rw [← hcallData]
          rw [eraseOccurrenceSlice_read]
          cases hfirst : call.data.read? (Int.ofNat right.base) with
          | none => simp
          | some firstB =>
            simp only [Option.map_some]
            have hgallopRight :
              gallopRight? (eraseOccurrenceMergeState call)
                (eraseOccurrenceSlice call.data)
                (Int.ofNat left.base) firstB.key.value
                left.len.toNat 0 =
                gallopRight? call call.data (Int.ofNat left.base)
                  firstB.key left.len.toNat 0 := by
              simpa [call] using
                (eraseOccurrenceGallopRight lt call call.data
                  (Int.ofNat left.base) firstB.key left.len.toNat 0
                  hcallCompare)
            simp only [eraseOccurrenceEntry_key]
            simp only [eraseOccurrenceMergeState] at hgallopRight
            rw [hgallopRight]
            cases htrimA : gallopRight? call call.data
              (Int.ofNat left.base) firstB.key left.len.toNat 0 with
            | none => simp
            | some trimA =>
              simp only [mergeAt_bindOptionAcross_some]
              by_cases htrimAFuel : trimA.fuelExhausted
              · simp [htrimAFuel, eraseOccurrenceMergeAtPreparation,
                eraseOccurrenceMergeAtResult,
                eraseOccurrenceMergeState, call]
              · rw [if_neg htrimAFuel, if_neg htrimAFuel]
                by_cases htrimABounds : left.len.toNat < trimA.index
                · simp [htrimABounds]
                · rw [if_neg htrimABounds, if_neg htrimABounds]
                  by_cases hemptyA : left.len.toNat - trimA.index = 0
                  · simp [hemptyA,
                    eraseOccurrenceMergeAtPreparation,
                    eraseOccurrenceMergeAtResult,
                    eraseOccurrenceMergeState, call]
                  · rw [if_neg hemptyA, if_neg hemptyA]
                    rw [eraseOccurrenceSlice_read]
                    cases hlast : call.data.read?
                      (Int.ofNat
                        (left.base + trimA.index +
                          (left.len.toNat - trimA.index) - 1)) with
                    | none => simp
                    | some lastA =>
                      simp only [Option.map_some]
                      have hgallopLeft :
                        gallopLeft?
                          (eraseOccurrenceMergeState call)
                          (eraseOccurrenceSlice call.data)
                          (Int.ofNat right.base) lastA.key.value
                          right.len.toNat
                          (right.len.toNat - 1) =
                          gallopLeft? call call.data
                            (Int.ofNat right.base) lastA.key
                            right.len.toNat
                            (right.len.toNat - 1) := by
                        simpa [call] using
                          (eraseOccurrenceGallopLeft lt call call.data
                            (Int.ofNat right.base) lastA.key
                            right.len.toNat (right.len.toNat - 1)
                            hcallCompare)
                      simp only [eraseOccurrenceEntry_key]
                      simp only [eraseOccurrenceMergeState] at hgallopLeft
                      rw [hgallopLeft]
                      cases htrimB : gallopLeft? call call.data
                        (Int.ofNat right.base) lastA.key
                        right.len.toNat (right.len.toNat - 1) with
                      | none => simp
                      | some trimB =>
                        simp only [mergeAt_bindOptionAcross_some]
                        by_cases htrimBFuel : trimB.fuelExhausted
                        · simp [htrimBFuel,
                          eraseOccurrenceMergeAtPreparation,
                          eraseOccurrenceMergeAtResult,
                          eraseOccurrenceMergeState, call]
                        · rw [if_neg htrimBFuel,
                          if_neg htrimBFuel]
                          by_cases htrimBBounds :
                            right.len.toNat < trimB.index
                          · simp [htrimBBounds]
                          · rw [if_neg htrimBBounds,
                            if_neg htrimBBounds]
                            by_cases hemptyB : trimB.index = 0
                            · simp [hemptyB,
                              eraseOccurrenceMergeAtPreparation,
                              eraseOccurrenceMergeAtResult,
                              eraseOccurrenceMergeState, call]
                            · rw [if_neg hemptyB, if_neg hemptyB]
                              by_cases hlo :
                                left.len.toNat - trimA.index ≤
                                  trimB.index
                              · simp [hlo,
                                eraseOccurrenceMergeAtPreparation,
                                eraseOccurrenceMergeAtCall,
                                eraseOccurrenceMergeState, call]
                              · simp [hlo,
                                eraseOccurrenceMergeAtPreparation,
                                eraseOccurrenceMergeAtCall,
                                eraseOccurrenceMergeState, call]
        · rw [if_neg hgeometry, if_neg hgeometry]
          rfl
  · simp [hposition]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceFinishMergeAtPreparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
lemma eraseOccurrenceFinishMergeAtPreparation
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {preparation : MergeAtPreparation (Occurrence alpha) nu}
-- given
  (hcompare : preparation.state.key_compare = occurrenceComparator lt) :
-- imply
  finishMergeAtPreparation? (eraseOccurrenceMergeAtPreparation preparation) = (finishMergeAtPreparation? preparation).map eraseOccurrenceMergeAtResult := by
-- proof
  cases preparation with
  | finished result => rfl
  | mergeLo call =>
    simp only [eraseOccurrenceMergeAtPreparation,
      finishMergeAtPreparation?, eraseOccurrenceMergeAtCall_state,
      eraseOccurrenceMergeAtCall_ssa, eraseOccurrenceMergeAtCall_ssb,
      eraseOccurrenceMergeAtCall_na, eraseOccurrenceMergeAtCall_nb]
    rw [eraseOccurrenceMergeLo lt call.state call.ssa call.ssb call.na
      call.nb hcompare]
    cases hmerge : mergeLo? call.state call.ssa call.ssb call.na call.nb with
    | none => rfl
    | some result =>
      simp [eraseOccurrenceMergeAtResult,
        eraseOccurrenceMergeLoResult]
  | mergeHi call =>
    simp only [eraseOccurrenceMergeAtPreparation,
      finishMergeAtPreparation?, eraseOccurrenceMergeAtCall_state,
      eraseOccurrenceMergeAtCall_ssa, eraseOccurrenceMergeAtCall_ssb,
      eraseOccurrenceMergeAtCall_na, eraseOccurrenceMergeAtCall_nb]
    rw [eraseOccurrenceMergeHi lt call.state call.ssa call.ssb call.na
      call.nb hcompare]
    cases hmerge : mergeHi? call.state call.ssa call.ssb call.na call.nb with
    | none => rfl
    | some result =>
      simp [eraseOccurrenceMergeAtResult,
        eraseOccurrenceMergeHiResult]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
lemma eraseOccurrenceMergeAt
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {state : MergeState (Occurrence alpha) nu}
  {i : Nat}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  mergeAt? (eraseOccurrenceMergeState state) i = (mergeAt? state i).map eraseOccurrenceMergeAtResult := by
-- proof
  unfold mergeAt?
  rw [eraseOccurrencePrepareMergeAt lt state i hcompare]
  cases hprepare : prepareMergeAt? state i with
  | none => rfl
  | some preparation =>
    simp only [Option.map_some, mergeAt_bindOptionAcross_some]
    apply eraseOccurrenceFinishMergeAtPreparation lt preparation
    rwa [prepareMergeAt?_key_compare_of_eq_some state i preparation hprepare]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceInitialMergeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
lemma eraseOccurrenceInitialMergeState
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {input : SortSlice alpha nu}
-- given
  (hasKeyfunc : Bool) :
-- imply
  eraseOccurrenceMergeState (initialMergeState (occurrenceComparator lt) hasKeyfunc (tagSortSliceOccurrences input)).1 = (initialMergeState lt hasKeyfunc input).1 := by
-- proof
  simp [initialMergeState, eraseOccurrenceMergeState,
    eraseOccurrenceTempStorage, mergeInitTemp]

end CPythonListsort

namespace CPythonListsort

/--
[initialMergeState_occurrence_stopped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
lemma initialMergeState_occurrence_stopped
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {input : SortSlice alpha nu}
-- given
  (hasKeyfunc : Bool) :
-- imply
  (initialMergeState (occurrenceComparator lt) hasKeyfunc (tagSortSliceOccurrences input)).2 = (initialMergeState lt hasKeyfunc input).2 := by
-- proof
  simp [initialMergeState, tagSortSliceOccurrences]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceFinishListSort](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
lemma eraseOccurrenceFinishListSort
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu}
  {reverse : Bool}
  {inputSize : Nat}
  {returnCode : Int}
  {fuelExhausted : Bool} :
-- imply
  finishListSort? (eraseOccurrenceMergeState state) reverse inputSize returnCode fuelExhausted = (finishListSort? state reverse inputSize returnCode fuelExhausted).map eraseOccurrenceListSortImplResult := by
-- proof
  unfold finishListSort?
  by_cases hreverse : reverse && decide (1 < inputSize)
  · rw [if_pos hreverse, if_pos hreverse]
    simp only [eraseOccurrenceMergeState_data]
    rw [eraseOccurrenceSortsliceReverse]
    cases hreversed : sortsliceReverse? state.data 0 inputSize with
    | none => simp
    | some reversed =>
      simp only [Option.map_some, bind, Option.bind,
        eraseOccurrenceReverseSliceResult]
      rw [eraseOccurrenceMergeState_setData, eraseOccurrenceMergeFreemem]
      rfl
  · rw [if_neg hreverse, if_neg hreverse]
    simp only [bind, Option.bind]
    rw [eraseOccurrenceMergeFreemem]
    rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceFailFromFoundNewRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
lemma eraseOccurrenceFailFromFoundNewRun
  {alpha : Type u}
  {nu : Type v}
  {result : FoundNewRunResult (Occurrence alpha) nu}
  {reverse : Bool}
  {inputSize : Nat} :
-- imply
  failFromFoundNewRun? (eraseOccurrenceFoundNewRunResult result) reverse inputSize = (failFromFoundNewRun? result reverse inputSize).map eraseOccurrenceListSortImplResult := by
-- proof
  simp [failFromFoundNewRun?]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceFailFromCollapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
lemma eraseOccurrenceFailFromCollapse
  {alpha : Type u}
  {nu : Type v}
  {result : MergeForceCollapseResult (Occurrence alpha) nu}
  {reverse : Bool}
  {inputSize : Nat} :
-- imply
  failFromCollapse? (eraseOccurrenceMergeForceCollapseResult result) reverse inputSize = (failFromCollapse? result reverse inputSize).map eraseOccurrenceListSortImplResult := by
-- proof
  simp [failFromCollapse?]

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[listSortScan_succ_of_remaining_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma listSortScan_succ_of_remaining_ne_zero {kappa : Type u}
  (fuel : Nat) (state : MergeState kappa nu)
  (lo remaining : Nat) (reverse : Bool) (inputSize : Nat)
  (hremaining : remaining ≠ 0) :
  listSortScan? (fuel + 1) state lo remaining reverse inputSize = (do
    let counted ← countRun? state state.data (Int.ofNat lo) remaining
    listSortScanAfterCount? fuel state lo remaining reverse inputSize
      counted) := by
  unfold listSortScan?
  rw [if_neg hremaining]
  unfold listSortScanAfterCount? listSortScanAfterExtension?
  apply Option.bind_congr
  intro counted _
  by_cases hcountFuel : counted.fuelExhausted
  · simp [hcountFuel]
  · simp only [hcountFuel]
    by_cases hcountBad : counted.length = 0 ∨ remaining < counted.length
    · simp [hcountBad]
    · simp only [hcountBad, if_false]
      let countedState : MergeState kappa nu :=
        { state with data := counted.slice }
      let nextMinrun := minrunNext countedState.minrunState
      let nextState := installMinrunState countedState nextMinrun.state
      let runLength := counted.length
      let target := nextMinrun.result.toNat
      by_cases hextend :
        (BitVec.ofNat 64 runLength : PySSize).slt nextMinrun.result
      · have hextendBase :
        (BitVec.ofNat 64 counted.length : PySSize).slt
          (minrunNext
            ({ state with data := counted.slice } :
              MergeState kappa nu).minrunState).result := by
        simpa only [runLength, nextMinrun, countedState] using hextend
        simp only [hextendBase, if_true]
        by_cases hforce : remaining ≤ target
        · have hforceBase :
          remaining ≤
            (minrunNext
              ({ state with data := counted.slice } :
                MergeState kappa nu).minrunState).result.toNat := by
          simpa only [target, nextMinrun, countedState] using hforce
          simp only [hforceBase, if_true]
          cases hsorted : binarysort? nextState nextState.data (Int.ofNat lo)
            remaining runLength with
          | none => simp
          | some sorted =>
            simp [hremaining]
            split <;> simp_all
            split <;> simp_all
        · have hforceBase :
          ¬ remaining ≤
            (minrunNext
              ({ state with data := counted.slice } :
                MergeState kappa nu).minrunState).result.toNat := by
          simpa only [target, nextMinrun, countedState] using hforce
          simp only [hforceBase, if_false]
          cases hsorted : binarysort? nextState nextState.data (Int.ofNat lo)
            target runLength with
          | none => simp
          | some sorted =>
            simp
            split <;> simp_all
            split <;> simp_all
            split <;> simp_all
      · have hextendBase :
        ¬ (BitVec.ofNat 64 counted.length : PySSize).slt
          (minrunNext
            ({ state with data := counted.slice } :
              MergeState kappa nu).minrunState).result := by
        simpa only [runLength, nextMinrun, countedState] using hextend
        simp [hextendBase, hcountBad]
        split <;> simp_all

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[eraseOccurrenceFoundNewRunLoop_of_mergeAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceFoundNewRunLoop_of_mergeAt
  (lt : BoolComparator alpha) (fuel : Nat)
  (state : MergeState (Occurrence alpha) nu) (power : Nat)
  (hcompare : state.key_compare = occurrenceComparator lt)
  (hmergeAt : ∀ (next : MergeState (Occurrence alpha) nu) (i : Nat),
    next.key_compare = occurrenceComparator lt →
      mergeAt? (eraseOccurrenceMergeState next) i =
        (mergeAt? next i).map eraseOccurrenceMergeAtResult) :
  foundNewRunLoop? fuel (eraseOccurrenceMergeState state) power =
    (foundNewRunLoop? fuel state power).map
      eraseOccurrenceFoundNewRunResult := by
  induction fuel generalizing state with
  | zero =>
    simp [foundNewRunLoop?, foundNewRunOutOfFuel_eq,
      eraseOccurrenceFoundNewRunResult, eraseOccurrenceMergeState]
  | succ fuel ih =>
    simp only [eraseOccurrenceMergeState]
    simp only [foundNewRunLoop?]
    by_cases hdepth : 1 < state.pending.size
    · rw [if_pos hdepth, if_pos hdepth]
      cases hpreceding : state.pending[state.pending.size - 2]? with
      | none => simp
      | some preceding =>
        simp only
        cases hpower : preceding.power with
        | none => simp
        | some precedingPower =>
          simp only
          by_cases hcollapse : power < precedingPower
          · rw [if_pos hcollapse, if_pos hcollapse]
            have heraseMerge := hmergeAt state
              (state.pending.size - 2) hcompare
            simp only [eraseOccurrenceMergeState] at heraseMerge
            rw [heraseMerge]
            cases hmerge : mergeAt? state
              (state.pending.size - 2) with
            | none => simp
            | some merged =>
              simp only [Option.map_some,
                eraseOccurrenceMergeAtResult_returnCode,
                eraseOccurrenceMergeAtResult_fuelExhausted]
              simp only [eraseOccurrenceMergeAtResult]
              split
              · rename_i hok
                simp only [hok]
                apply ih
                exact
                  (mergeAt?_key_compare_of_eq_some state
                    (state.pending.size - 2) merged hmerge).trans
                    hcompare
              · rename_i hok
                simp only [hok, if_false]
                simp [foundNewRunFromMergeAt_eq,
                  eraseOccurrenceFoundNewRunResult]
          · rw [if_neg hcollapse, if_neg hcollapse]
            have heraseSet := eraseOccurrenceSetTopPower power state
            simp only [eraseOccurrenceMergeState] at heraseSet
            rw [heraseSet]
            cases hset : setTopPower? state power with
            | none => simp
            | some updated =>
              simp [foundNewRunSuccess_eq,
                eraseOccurrenceFoundNewRunResult]
    · rw [if_neg hdepth, if_neg hdepth]
      have heraseSet := eraseOccurrenceSetTopPower power state
      simp only [eraseOccurrenceMergeState] at heraseSet
      rw [heraseSet]
      cases hset : setTopPower? state power with
      | none => simp
      | some updated =>
        simp [foundNewRunSuccess_eq, eraseOccurrenceFoundNewRunResult]

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[eraseOccurrenceFoundNewRun_of_mergeAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceFoundNewRun_of_mergeAt
  (lt : BoolComparator alpha)
  (state : MergeState (Occurrence alpha) nu) (n2 : Nat)
  (hcompare : state.key_compare = occurrenceComparator lt)
  (hmergeAt : ∀ (next : MergeState (Occurrence alpha) nu) (i : Nat),
    next.key_compare = occurrenceComparator lt →
      mergeAt? (eraseOccurrenceMergeState next) i =
        (mergeAt? next i).map eraseOccurrenceMergeAtResult) :
  foundNewRun? (eraseOccurrenceMergeState state) n2 =
    (foundNewRun? state n2).map eraseOccurrenceFoundNewRunResult := by
  simp only [eraseOccurrenceMergeState]
  unfold foundNewRun?
  by_cases hempty : state.pending.isEmpty
  · simp [hempty, foundNewRunSuccess_eq,
    eraseOccurrenceFoundNewRunResult, eraseOccurrenceMergeState]
  · rw [if_neg hempty, if_neg hempty]
    cases htop : state.pending[state.pending.size - 1]? with
    | none => simp
    | some top =>
      simp only
      split
      · rename_i hguard
        let traced := powerloopTraced
          (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
          (BitVec.ofNat 64 n2) state.listlen
        by_cases hstopped : !traced.stopped
        · simp [traced, hstopped, foundNewRunOutOfFuel_eq,
          eraseOccurrenceFoundNewRunResult, eraseOccurrenceMergeState]
        · rw [if_neg hstopped, if_neg hstopped]
          have hloop := eraseOccurrenceFoundNewRunLoop_of_mergeAt lt
            state.pending.size state traced.result hcompare hmergeAt
          simpa [traced, eraseOccurrenceMergeState] using hloop
      · rename_i hguard
        simp only [Option.map_none]

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[eraseOccurrenceMergeForceCollapseLoop_of_mergeAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceMergeForceCollapseLoop_of_mergeAt
  (lt : BoolComparator alpha) (fuel : Nat)
  (state : MergeState (Occurrence alpha) nu)
  (hcompare : state.key_compare = occurrenceComparator lt)
  (hmergeAt : ∀ (next : MergeState (Occurrence alpha) nu) (i : Nat),
    next.key_compare = occurrenceComparator lt →
      mergeAt? (eraseOccurrenceMergeState next) i =
        (mergeAt? next i).map eraseOccurrenceMergeAtResult) :
  mergeForceCollapseLoop? fuel (eraseOccurrenceMergeState state) =
    (mergeForceCollapseLoop? fuel state).map
      eraseOccurrenceMergeForceCollapseResult := by
  induction fuel generalizing state with
  | zero =>
    simp only [eraseOccurrenceMergeState]
    simp only [mergeForceCollapseLoop?]
    split <;> rfl
  | succ fuel ih =>
    simp only [eraseOccurrenceMergeState]
    simp only [mergeForceCollapseLoop?]
    by_cases hdepth : 1 < state.pending.size
    · rw [if_pos hdepth, if_pos hdepth]
      have heraseIndex := eraseOccurrenceForceCollapseIndex state
      simp only [eraseOccurrenceMergeState] at heraseIndex
      rw [heraseIndex]
      cases hindex : forceCollapseIndex? state with
      | none => simp
      | some i =>
        simp only
        have heraseMerge := hmergeAt state i hcompare
        simp only [eraseOccurrenceMergeState] at heraseMerge
        rw [heraseMerge]
        cases hmerge : mergeAt? state i with
        | none => simp
        | some merged =>
          simp only [Option.map_some,
            eraseOccurrenceMergeAtResult_returnCode,
            eraseOccurrenceMergeAtResult_fuelExhausted]
          simp only [eraseOccurrenceMergeAtResult]
          split
          · rename_i hok
            simp only [hok]
            apply ih
            exact
              (mergeAt?_key_compare_of_eq_some state i merged
                hmerge).trans hcompare
          · rename_i hok
            simp only [hok, if_false]
            rfl
    · rw [if_neg hdepth, if_neg hdepth]
      rfl

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[eraseOccurrenceMergeForceCollapse_of_mergeAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceMergeForceCollapse_of_mergeAt
  (lt : BoolComparator alpha)
  (state : MergeState (Occurrence alpha) nu)
  (hcompare : state.key_compare = occurrenceComparator lt)
  (hmergeAt : ∀ (next : MergeState (Occurrence alpha) nu) (i : Nat),
    next.key_compare = occurrenceComparator lt →
      mergeAt? (eraseOccurrenceMergeState next) i =
        (mergeAt? next i).map eraseOccurrenceMergeAtResult) :
  mergeForceCollapse? (eraseOccurrenceMergeState state) =
    (mergeForceCollapse? state).map
      eraseOccurrenceMergeForceCollapseResult := by
  unfold mergeForceCollapse?
  rw [eraseOccurrenceMergeState_pending]
  exact eraseOccurrenceMergeForceCollapseLoop_of_mergeAt lt
    state.pending.size state hcompare hmergeAt

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[eraseOccurrenceListSortScanAfterExtension_of_mergeAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceListSortScanAfterExtension_of_mergeAt
  (lt : BoolComparator alpha) (fuel : Nat)
  (state : MergeState (Occurrence alpha) nu) (lo remaining : Nat)
  (reverse : Bool) (inputSize runLength : Nat) (extensionFuel : Bool)
  (hcompare : state.key_compare = occurrenceComparator lt)
  (hmergeAt : ∀ (next : MergeState (Occurrence alpha) nu) (i : Nat),
    next.key_compare = occurrenceComparator lt →
      mergeAt? (eraseOccurrenceMergeState next) i =
        (mergeAt? next i).map eraseOccurrenceMergeAtResult)
  (hscan : ∀ (nextState : MergeState (Occurrence alpha) nu)
    (nextLo nextRemaining : Nat),
    nextState.key_compare = occurrenceComparator lt →
      listSortScan? fuel (eraseOccurrenceMergeState nextState) nextLo
        nextRemaining reverse inputSize =
        (listSortScan? fuel nextState nextLo nextRemaining reverse
          inputSize).map eraseOccurrenceListSortImplResult) :
  listSortScanAfterExtension? fuel (eraseOccurrenceMergeState state) lo
    remaining reverse inputSize runLength extensionFuel =
    (listSortScanAfterExtension? fuel state lo remaining reverse inputSize
      runLength extensionFuel).map eraseOccurrenceListSortImplResult := by
  unfold listSortScanAfterExtension?
  by_cases hextFuel : extensionFuel
  · rw [if_pos hextFuel, if_pos hextFuel]
    exact eraseOccurrenceFinishListSort state reverse inputSize (-1) true
  · rw [if_neg hextFuel, if_neg hextFuel]
    by_cases hbad : runLength = 0 ∨ remaining < runLength
    · simp [hbad]
    · rw [if_neg hbad, if_neg hbad]
      rw [eraseOccurrenceFoundNewRun_of_mergeAt lt state runLength hcompare
        hmergeAt]
      cases hfound : foundNewRun? state runLength with
      | none => simp
      | some found =>
        simp only [Option.map_some,
          eraseOccurrenceFoundNewRunResult_returnCode,
          eraseOccurrenceFoundNewRunResult_fuelExhausted]
        simp only [eraseOccurrenceFoundNewRunResult]
        split
        · rename_i hok
          simp only [hok, eraseOccurrencePushPendingRun]
          apply hscan
          exact
            (foundNewRun?_key_compare_of_eq_some state runLength found
              hfound).trans hcompare
        · rename_i hok
          simp only [hok, if_false]
          exact eraseOccurrenceFailFromFoundNewRun found reverse inputSize

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[eraseOccurrenceListSortScanAfterCount_of_mergeAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceListSortScanAfterCount_of_mergeAt
  (lt : BoolComparator alpha) (fuel : Nat)
  (state : MergeState (Occurrence alpha) nu) (lo remaining : Nat)
  (reverse : Bool) (inputSize : Nat)
  (counted : CountRunResult (Occurrence alpha) nu)
  (hcompare : state.key_compare = occurrenceComparator lt)
  (hmergeAt : ∀ (next : MergeState (Occurrence alpha) nu) (i : Nat),
    next.key_compare = occurrenceComparator lt →
      mergeAt? (eraseOccurrenceMergeState next) i =
        (mergeAt? next i).map eraseOccurrenceMergeAtResult)
  (hscan : ∀ (nextState : MergeState (Occurrence alpha) nu)
    (nextLo nextRemaining : Nat),
    nextState.key_compare = occurrenceComparator lt →
      listSortScan? fuel (eraseOccurrenceMergeState nextState) nextLo
        nextRemaining reverse inputSize =
        (listSortScan? fuel nextState nextLo nextRemaining reverse
          inputSize).map eraseOccurrenceListSortImplResult) :
  listSortScanAfterCount? fuel (eraseOccurrenceMergeState state) lo remaining
    reverse inputSize (eraseOccurrenceCountRunResult counted) =
    (listSortScanAfterCount? fuel state lo remaining reverse inputSize
      counted).map eraseOccurrenceListSortImplResult := by
  unfold listSortScanAfterCount?
  simp only [eraseOccurrenceCountRunResult_slice,
    eraseOccurrenceCountRunResult_length, eraseOccurrenceCountRunResult_fuel,
    eraseOccurrenceMergeState_setData]
  set countedState : MergeState (Occurrence alpha) nu :=
    { state with data := counted.slice }
  have hcountedCompare :
    countedState.key_compare = occurrenceComparator lt := hcompare
  by_cases hcountFuel : counted.fuelExhausted
  · rw [if_pos hcountFuel, if_pos hcountFuel]
    exact eraseOccurrenceFinishListSort countedState reverse inputSize (-1) true
  · rw [if_neg hcountFuel, if_neg hcountFuel]
    by_cases hcountBad : counted.length = 0 ∨ remaining < counted.length
    · simp [hcountBad]
    · rw [if_neg hcountBad, if_neg hcountBad]
      let nextMinrun := minrunNext countedState.minrunState
      let nextState := installMinrunState countedState nextMinrun.state
      have hnextCompare :
        nextState.key_compare = occurrenceComparator lt := hcountedCompare
      let runLength := counted.length
      let target := nextMinrun.result.toNat
      let force := if remaining ≤ target then remaining else target
      by_cases hextend :
        (BitVec.ofNat 64 runLength : PySSize).slt nextMinrun.result
      · have hextendBase :
        (BitVec.ofNat 64 counted.length : PySSize).slt
          (minrunNext countedState.minrunState).result := by
        simpa only [runLength, nextMinrun] using hextend
        have hextendErased :
          (BitVec.ofNat 64 counted.length : PySSize).slt
            (minrunNext
              (eraseOccurrenceMergeState countedState).minrunState).result := by
          simpa only [eraseOccurrenceMergeState_minrunState] using hextendBase
        rw [if_pos hextendErased, if_pos hextendBase]
        by_cases hforce : remaining ≤ target
        · have hforceBase :
          remaining ≤
            (minrunNext countedState.minrunState).result.toNat := by
          simpa only [target, nextMinrun] using hforce
          have hforceErased :
            remaining ≤ (minrunNext
              (eraseOccurrenceMergeState countedState).minrunState).result.toNat := by
            simpa only [eraseOccurrenceMergeState_minrunState] using hforceBase
          simp only [if_pos hforceErased, if_pos hforceBase]
          simp only [eraseOccurrenceMergeState_minrunState,
            eraseOccurrenceInstallMinrunState,
            eraseOccurrenceMergeState_data]
          rw [eraseOccurrenceBinarysort lt nextState nextState.data
            (Int.ofNat lo) remaining runLength hnextCompare]
          cases hsorted : binarysort? nextState nextState.data (Int.ofNat lo)
            remaining runLength with
          | none => simp
          | some sorted =>
            simp only [Option.map_some, bind, Option.bind,
              eraseOccurrenceBinarysortResult_slice,
              eraseOccurrenceBinarysortResult_fuel,
              eraseOccurrenceMergeState_setData]
            exact eraseOccurrenceListSortScanAfterExtension_of_mergeAt lt
              fuel { nextState with data := sorted.slice } lo remaining
              reverse inputSize remaining sorted.fuelExhausted hnextCompare
              hmergeAt hscan
        · have hforceBase :
          ¬ remaining ≤
            (minrunNext countedState.minrunState).result.toNat := by
          simpa only [target, nextMinrun] using hforce
          have hforceErased :
            ¬ remaining ≤ (minrunNext
              (eraseOccurrenceMergeState countedState).minrunState).result.toNat := by
            simpa only [eraseOccurrenceMergeState_minrunState] using hforceBase
          simp only [if_neg hforceErased, if_neg hforceBase]
          simp only [eraseOccurrenceMergeState_minrunState,
            eraseOccurrenceInstallMinrunState,
            eraseOccurrenceMergeState_data]
          rw [eraseOccurrenceBinarysort lt nextState nextState.data
            (Int.ofNat lo) target runLength hnextCompare]
          cases hsorted : binarysort? nextState nextState.data (Int.ofNat lo)
            target runLength with
          | none => simp
          | some sorted =>
            simp only [Option.map_some, bind, Option.bind,
              eraseOccurrenceBinarysortResult_slice,
              eraseOccurrenceBinarysortResult_fuel,
              eraseOccurrenceMergeState_setData]
            exact eraseOccurrenceListSortScanAfterExtension_of_mergeAt lt
              fuel { nextState with data := sorted.slice } lo remaining
              reverse inputSize target sorted.fuelExhausted hnextCompare
              hmergeAt hscan
      · have hextendBase :
        ¬ (BitVec.ofNat 64 counted.length : PySSize).slt
          (minrunNext countedState.minrunState).result := by
        simpa only [runLength, nextMinrun] using hextend
        have hextendErased :
          ¬ (BitVec.ofNat 64 counted.length : PySSize).slt
            (minrunNext
              (eraseOccurrenceMergeState countedState).minrunState).result := by
          simpa only [eraseOccurrenceMergeState_minrunState] using hextendBase
        rw [if_neg hextendErased, if_neg hextendBase]
        simp only [eraseOccurrenceMergeState_minrunState,
          eraseOccurrenceInstallMinrunState, eraseOccurrenceMergeState_data,
          bind, Option.bind, eraseOccurrenceMergeState_setData]
        exact eraseOccurrenceListSortScanAfterExtension_of_mergeAt lt fuel
          { nextState with data := nextState.data } lo remaining reverse
          inputSize runLength false hnextCompare hmergeAt hscan

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[eraseOccurrenceListSortScan_of_mergeAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceListSortScan_of_mergeAt
  (lt : BoolComparator alpha) (fuel : Nat)
  (state : MergeState (Occurrence alpha) nu) (lo remaining : Nat)
  (reverse : Bool) (inputSize : Nat)
  (hcompare : state.key_compare = occurrenceComparator lt)
  (hmergeAt : ∀ (next : MergeState (Occurrence alpha) nu) (i : Nat),
    next.key_compare = occurrenceComparator lt →
      mergeAt? (eraseOccurrenceMergeState next) i =
        (mergeAt? next i).map eraseOccurrenceMergeAtResult) :
  listSortScan? fuel (eraseOccurrenceMergeState state) lo remaining reverse
    inputSize =
    (listSortScan? fuel state lo remaining reverse inputSize).map
      eraseOccurrenceListSortImplResult := by
  induction fuel generalizing state lo remaining with
  | zero =>
    simp only [listSortScan?]
    by_cases hremaining : remaining = 0
    · rw [if_pos hremaining, if_pos hremaining]
      have heraseCollapse :=
        eraseOccurrenceMergeForceCollapse_of_mergeAt lt state hcompare
          hmergeAt
      rw [heraseCollapse]
      cases hcollapse : mergeForceCollapse? state with
      | none => simp
      | some collapsed =>
        simp only [Option.map_some,
          eraseOccurrenceMergeForceCollapseResult_returnCode,
          eraseOccurrenceMergeForceCollapseResult_fuelExhausted]
        simp only [eraseOccurrenceMergeForceCollapseResult]
        split
        · rename_i hok
          simp only [hok]
          exact eraseOccurrenceFinishListSort collapsed.state reverse
            inputSize 0 false
        · rename_i hok
          simp only [hok, if_false]
          exact eraseOccurrenceFailFromCollapse collapsed reverse inputSize
    · rw [if_neg hremaining, if_neg hremaining]
      exact eraseOccurrenceFinishListSort state reverse inputSize (-1) true
  | succ fuel ih =>
    by_cases hremaining : remaining = 0
    · simp only [listSortScan?]
      rw [if_pos hremaining, if_pos hremaining]
      have heraseCollapse :=
        eraseOccurrenceMergeForceCollapse_of_mergeAt lt state hcompare
          hmergeAt
      rw [heraseCollapse]
      cases hcollapse : mergeForceCollapse? state with
      | none => simp
      | some collapsed =>
        simp only [Option.map_some,
          eraseOccurrenceMergeForceCollapseResult_returnCode,
          eraseOccurrenceMergeForceCollapseResult_fuelExhausted]
        simp only [eraseOccurrenceMergeForceCollapseResult]
        split
        · rename_i hok
          simp only [hok]
          exact eraseOccurrenceFinishListSort collapsed.state reverse
            inputSize 0 false
        · rename_i hok
          simp only [hok, if_false]
          exact eraseOccurrenceFailFromCollapse collapsed reverse inputSize
    · have herasedStep :=
      listSortScan_succ_of_remaining_ne_zero fuel
        (eraseOccurrenceMergeState state) lo remaining reverse inputSize
        hremaining
      have hbaseStep :=
        listSortScan_succ_of_remaining_ne_zero fuel state lo remaining
          reverse inputSize hremaining
      rw [herasedStep, hbaseStep]
      have heraseCount := eraseOccurrenceCountRun lt state state.data
        (Int.ofNat lo) remaining hcompare
      rw [eraseOccurrenceMergeState_data]
      rw [heraseCount]
      cases hcount : countRun? state state.data (Int.ofNat lo) remaining with
      | none => simp
      | some counted =>
        simp only [Option.map_some, bind, Option.bind]
        have htail := eraseOccurrenceListSortScanAfterCount_of_mergeAt lt
          fuel state lo remaining reverse inputSize counted hcompare
          hmergeAt
          (fun nextState nextLo nextRemaining hnextCompare =>
            ih nextState nextLo nextRemaining hnextCompare)
        exact htail

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceFoundNewRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
lemma eraseOccurrenceFoundNewRun
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {state : MergeState (Occurrence alpha) nu}
  {n2 : Nat}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  foundNewRun? (eraseOccurrenceMergeState state) n2 = (foundNewRun? state n2).map eraseOccurrenceFoundNewRunResult := by
-- proof
  exact eraseOccurrenceFoundNewRun_of_mergeAt lt state n2 hcompare
    (fun next i hnext => eraseOccurrenceMergeAt lt next i hnext)

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeForceCollapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
lemma eraseOccurrenceMergeForceCollapse
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {state : MergeState (Occurrence alpha) nu}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  mergeForceCollapse? (eraseOccurrenceMergeState state) = (mergeForceCollapse? state).map eraseOccurrenceMergeForceCollapseResult := by
-- proof
  exact eraseOccurrenceMergeForceCollapse_of_mergeAt lt state hcompare
    (fun next i hnext => eraseOccurrenceMergeAt lt next i hnext)

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceListSortScan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
lemma eraseOccurrenceListSortScan
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {fuel : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {lo remaining : Nat}
  {reverse : Bool}
  {inputSize : Nat}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  listSortScan? fuel (eraseOccurrenceMergeState state) lo remaining reverse inputSize = (listSortScan? fuel state lo remaining reverse inputSize).map eraseOccurrenceListSortImplResult := by
-- proof
  exact eraseOccurrenceListSortScan_of_mergeAt lt fuel state lo remaining
    reverse inputSize hcompare
    (fun next i hnext => eraseOccurrenceMergeAt lt next i hnext)

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceListSortImpl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
lemma eraseOccurrenceListSortImpl
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {input : SortSlice alpha nu}
-- given
  (reverse hasKeyfunc : Bool) :
-- imply
  listSortImpl? lt reverse hasKeyfunc input = (listSortImpl? (occurrenceComparator lt) reverse hasKeyfunc (tagSortSliceOccurrences input)).map eraseOccurrenceListSortImplResult := by
-- proof
  unfold listSortImpl?
  simp only [tagSortSliceOccurrences_size]
  by_cases hmax : input.entries.size ≤ PY_LIST_MAX
  · rw [if_pos hmax, if_pos hmax]
    rw [← eraseOccurrenceInitialMergeState lt hasKeyfunc input]
    rw [← initialMergeState_occurrence_stopped lt hasKeyfunc input]
    set taggedState :=
      (initialMergeState (occurrenceComparator lt) hasKeyfunc
        (tagSortSliceOccurrences input)).1
    set stopped :=
      (initialMergeState (occurrenceComparator lt) hasKeyfunc
        (tagSortSliceOccurrences input)).2
    have hcompare : taggedState.key_compare = occurrenceComparator lt := by
      simp [taggedState, initialMergeState]
    by_cases hstop : (!stopped) = true
    · rw [if_pos hstop, if_pos hstop]
      exact eraseOccurrenceFinishListSort taggedState reverse
        input.entries.size (-1) true
    · rw [if_neg hstop, if_neg hstop]
      by_cases hsmall : input.entries.size < 2
      · rw [if_pos hsmall, if_pos hsmall]
        exact eraseOccurrenceFinishListSort taggedState reverse
          input.entries.size 0 false
      · rw [if_neg hsmall, if_neg hsmall]
        by_cases hreverse : reverse = true
        · rw [if_pos hreverse, if_pos hreverse]
          rw [eraseOccurrenceMergeState_data,
            eraseOccurrenceSortsliceReverse]
          cases hreversed : sortsliceReverse? taggedState.data 0
            input.entries.size with
          | none => simp
          | some reversed =>
            simp only [Option.map_some,
              eraseOccurrenceReverseSliceResult]
            rw [eraseOccurrenceMergeState_setData]
            by_cases hexhausted : reversed.fuelExhausted = true
            · rw [if_pos hexhausted, if_pos hexhausted]
              exact eraseOccurrenceFinishListSort
                { taggedState with data := reversed.slice } reverse
                input.entries.size (-1) true
            · rw [if_neg hexhausted, if_neg hexhausted]
              apply eraseOccurrenceListSortScan lt input.entries.size
                { taggedState with data := reversed.slice } 0
                input.entries.size reverse input.entries.size
              exact hcompare
        · rw [if_neg hreverse, if_neg hreverse]
          exact eraseOccurrenceListSortScan lt input.entries.size taggedState
            0 input.entries.size reverse input.entries.size hcompare
  · simp [hmax]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceListSort](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
lemma eraseOccurrenceListSort
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {reverse : Bool}
  {input : ListSortInput alpha nu} :
-- imply
  listSort? lt reverse input = (listSort? (occurrenceComparator lt) reverse input.withOccurrenceKeys).map eraseOccurrenceListSortImplResult := by
-- proof
  unfold listSort?
  simpa only [ListSortInput.withOccurrenceKeys] using
    eraseOccurrenceListSortImpl lt reverse input.hasKeyfunc input.slice

end CPythonListsort

/--
[eraseOccurrenceMergeAtResult_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceMergeAtResult_state_eq
  {alpha : Type u}
  {nu : Type v}
  {result : MergeAtResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeAtResult result).state = eraseOccurrenceMergeState result.state := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeAtResult_state result

/--
[eraseOccurrenceMergeAtResult_returnCode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceMergeAtResult_returnCode_eq
  {alpha : Type u}
  {nu : Type v}
  {result : MergeAtResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeAtResult result).returnCode = result.returnCode := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeAtResult_returnCode result

/--
[eraseOccurrenceMergeAtResult_fuelExhausted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceMergeAtResult_fuelExhausted_eq
  {alpha : Type u}
  {nu : Type v}
  {result : MergeAtResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeAtResult result).fuelExhausted = result.fuelExhausted := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeAtResult_fuelExhausted result

/--
[eraseOccurrenceMergeAtCall_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceMergeAtCall_state_eq
  {alpha : Type u}
  {nu : Type v}
  {call : MergeAtCall (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeAtCall call).state = eraseOccurrenceMergeState call.state := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeAtCall_state call

/--
[eraseOccurrenceMergeAtCall_firstB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceMergeAtCall_firstB_eq
  {alpha : Type u}
  {nu : Type v}
  {call : MergeAtCall (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeAtCall call).firstB = eraseOccurrenceEntry call.firstB := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeAtCall_firstB call

/--
[eraseOccurrenceMergeAtCall_lastA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceMergeAtCall_lastA_eq
  {alpha : Type u}
  {nu : Type v}
  {call : MergeAtCall (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeAtCall call).lastA = eraseOccurrenceEntry call.lastA := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeAtCall_lastA call

/--
[eraseOccurrenceMergeAtCall_ssa](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceMergeAtCall_ssa_eq
  {alpha : Type u}
  {nu : Type v}
  {call : MergeAtCall (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeAtCall call).ssa = call.ssa := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeAtCall_ssa call

/--
[eraseOccurrenceMergeAtCall_ssb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceMergeAtCall_ssb_eq
  {alpha : Type u}
  {nu : Type v}
  {call : MergeAtCall (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeAtCall call).ssb = call.ssb := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeAtCall_ssb call

/--
[eraseOccurrenceMergeAtCall_na](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceMergeAtCall_na_eq
  {alpha : Type u}
  {nu : Type v}
  {call : MergeAtCall (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeAtCall call).na = call.na := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeAtCall_na call

/--
[eraseOccurrenceMergeAtCall_nb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceMergeAtCall_nb_eq
  {alpha : Type u}
  {nu : Type v}
  {call : MergeAtCall (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeAtCall call).nb = call.nb := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeAtCall_nb call

/--
[eraseOccurrenceMergeAtPreparation_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceMergeAtPreparation_state_eq
  {alpha : Type u}
  {nu : Type v}
  {preparation : MergeAtPreparation (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeAtPreparation preparation).state = eraseOccurrenceMergeState preparation.state := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeAtPreparation_state preparation

/--
[eraseOccurrenceFoundNewRunResult_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceFoundNewRunResult_state_eq
  {alpha : Type u}
  {nu : Type v}
  {result : FoundNewRunResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceFoundNewRunResult result).state = eraseOccurrenceMergeState result.state := by
-- proof
  apply CPythonListsort.eraseOccurrenceFoundNewRunResult_state result

/--
[eraseOccurrenceFoundNewRunResult_returnCode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceFoundNewRunResult_returnCode_eq
  {alpha : Type u}
  {nu : Type v}
  {result : FoundNewRunResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceFoundNewRunResult result).returnCode = result.returnCode := by
-- proof
  apply CPythonListsort.eraseOccurrenceFoundNewRunResult_returnCode result

/--
[eraseOccurrenceFoundNewRunResult_fuelExhausted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceFoundNewRunResult_fuelExhausted_eq
  {alpha : Type u}
  {nu : Type v}
  {result : FoundNewRunResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceFoundNewRunResult result).fuelExhausted = result.fuelExhausted := by
-- proof
  apply CPythonListsort.eraseOccurrenceFoundNewRunResult_fuelExhausted result

/--
[eraseOccurrenceMergeForceCollapseResult_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceMergeForceCollapseResult_state_eq
  {alpha : Type u}
  {nu : Type v}
  {result : MergeForceCollapseResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeForceCollapseResult result).state = eraseOccurrenceMergeState result.state := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeForceCollapseResult_state result

/--
[eraseOccurrenceMergeForceCollapseResult_returnCode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceMergeForceCollapseResult_returnCode_eq
  {alpha : Type u}
  {nu : Type v}
  {result : MergeForceCollapseResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeForceCollapseResult result).returnCode = result.returnCode := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeForceCollapseResult_returnCode result

/--
[eraseOccurrenceMergeForceCollapseResult_fuelExhausted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureScan.lean)
-/
@[path]
private lemma eraseOccurrenceMergeForceCollapseResult_fuelExhausted_eq
  {alpha : Type u}
  {nu : Type v}
  {result : MergeForceCollapseResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeForceCollapseResult result).fuelExhausted = result.fuelExhausted := by
-- proof
  apply CPythonListsort.eraseOccurrenceMergeForceCollapseResult_fuelExhausted result


-- created on 2026-10-23

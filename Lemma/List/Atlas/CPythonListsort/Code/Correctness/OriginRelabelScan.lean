import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.CPythonListsort.Code.Correctness.OriginRelabelScan.Part2
open CPythonListsort


namespace CPythonListsort

/--
[mirrorPushPendingRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma mirrorPushPendingRun
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {run : PendingRun} :
-- imply
  pushPendingRun (mirrorMergeState size state) run = mirrorMergeState size (pushPendingRun state run) := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mirrorInstallMinrunState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma mirrorInstallMinrunState
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {minrun : MinrunState} :
-- imply
  installMinrunState (mirrorMergeState size state) minrun = mirrorMergeState size (installMinrunState state minrun) := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mirrorMergeState_setData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma mirrorMergeState_setData
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {data : SortSlice (Occurrence alpha) nu} :
-- imply
  { mirrorMergeState size state with data := mirrorSortSlice size data } = mirrorMergeState size { state with data := data } := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mirrorMergeState_setPending](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma mirrorMergeState_setPending
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {pending : Array PendingRun} :
-- imply
  { mirrorMergeState size state with pending := pending } = mirrorMergeState size { state with pending := pending } := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mirrorSetTopPower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma mirrorSetTopPower
  {alpha : Type u}
  {nu : Type v}
  {size power : Nat}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  setTopPower? (mirrorMergeState size state) power = (setTopPower? state power).map (mirrorMergeState size) := by
-- proof
  simp only [mirrorMergeState]
  unfold setTopPower?
  by_cases hempty : state.pending.isEmpty
  · simp [hempty]
  · rw [if_neg hempty, if_neg hempty]
    cases htop : state.pending[state.pending.size - 1]? with
    | none => simp [htop]
    | some top => simp [htop, mirrorMergeState]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorForceCollapseIndex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma mirrorForceCollapseIndex
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  forceCollapseIndex? (mirrorMergeState size state) = forceCollapseIndex? state := by
-- proof
  simp [forceCollapseIndex?, mirrorMergeState]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorPrepareMergeAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma mirrorPrepareMergeAt
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {i : Nat}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  prepareMergeAt? (mirrorMergeState size state) i = (prepareMergeAt? state i).map (mirrorMergeAtPreparation size) := by
-- proof
  simp only [mirrorMergeState]
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
          have hmirrorCall :
            { mirrorMergeState size state with
              pending :=
                (state.pending.setIfInBounds i
                  { left with len := left.len + right.len }).eraseIdxIfInBounds
                    (i + 1) } = mirrorMergeState size call := rfl
          have hmirrorCall' := hmirrorCall
          simp only [mirrorMergeState] at hmirrorCall'
          rw [hmirrorCall']
          have hcallCompare :
            call.key_compare = occurrenceComparator lt := hcompare
          have hcallData : call.data = state.data := rfl
          rw [← hcallData]
          rw [mirrorSortSlice_read]
          cases hfirst : call.data.read? (Int.ofNat right.base) with
          | none => simp
          | some firstB =>
            simp only [Option.map_some]
            have hgallopRight :
              gallopRight? (mirrorMergeState size call)
                (mirrorSortSlice size call.data)
                (Int.ofNat left.base)
                (mirrorOccurrence size firstB.key) left.len.toNat 0 =
                gallopRight? call call.data (Int.ofNat left.base)
                  firstB.key left.len.toNat 0 := by
              simpa [call] using
                (mirrorGallopRight lt size call call.data
                  (Int.ofNat left.base) firstB.key left.len.toNat 0
                  hcallCompare)
            simp only [mirrorSortSliceEntry_key]
            simp only [mirrorMergeState] at hgallopRight
            rw [hgallopRight]
            cases htrimA : gallopRight? call call.data
              (Int.ofNat left.base) firstB.key left.len.toNat 0 with
            | none => simp
            | some trimA =>
              simp only [mergeAt_bindOptionAcross_some]
              by_cases htrimAFuel : trimA.fuelExhausted
              · simp [htrimAFuel, mirrorMergeAtPreparation,
                mirrorMergeAtResult, mirrorMergeState, call]
              · rw [if_neg htrimAFuel, if_neg htrimAFuel]
                by_cases htrimABounds : left.len.toNat < trimA.index
                · simp [htrimABounds]
                · rw [if_neg htrimABounds, if_neg htrimABounds]
                  by_cases hemptyA : left.len.toNat - trimA.index = 0
                  · simp [hemptyA, mirrorMergeAtPreparation,
                    mirrorMergeAtResult, mirrorMergeState, call]
                  · rw [if_neg hemptyA, if_neg hemptyA]
                    rw [mirrorSortSlice_read]
                    cases hlast : call.data.read?
                      (Int.ofNat
                        (left.base + trimA.index +
                          (left.len.toNat - trimA.index) - 1)) with
                    | none => simp
                    | some lastA =>
                      simp only [Option.map_some]
                      have hgallopLeft :
                        gallopLeft? (mirrorMergeState size call)
                          (mirrorSortSlice size call.data)
                          (Int.ofNat right.base)
                          (mirrorOccurrence size lastA.key)
                          right.len.toNat
                          (right.len.toNat - 1) =
                          gallopLeft? call call.data
                            (Int.ofNat right.base) lastA.key
                            right.len.toNat
                            (right.len.toNat - 1) := by
                        simpa [call] using
                          (mirrorGallopLeft lt size call call.data
                            (Int.ofNat right.base) lastA.key
                            right.len.toNat (right.len.toNat - 1)
                            hcallCompare)
                      simp only [mirrorSortSliceEntry_key]
                      simp only [mirrorMergeState] at hgallopLeft
                      rw [hgallopLeft]
                      cases htrimB : gallopLeft? call call.data
                        (Int.ofNat right.base) lastA.key
                        right.len.toNat (right.len.toNat - 1) with
                      | none => simp
                      | some trimB =>
                        simp only [mergeAt_bindOptionAcross_some]
                        by_cases htrimBFuel : trimB.fuelExhausted
                        · simp [htrimBFuel,
                          mirrorMergeAtPreparation,
                          mirrorMergeAtResult, mirrorMergeState,
                          call]
                        · rw [if_neg htrimBFuel, if_neg htrimBFuel]
                          by_cases htrimBBounds :
                            right.len.toNat < trimB.index
                          · simp [htrimBBounds]
                          · rw [if_neg htrimBBounds,
                            if_neg htrimBBounds]
                            by_cases hemptyB : trimB.index = 0
                            · simp [hemptyB,
                              mirrorMergeAtPreparation,
                              mirrorMergeAtResult,
                              mirrorMergeState, call]
                            · rw [if_neg hemptyB, if_neg hemptyB]
                              by_cases hlo :
                                left.len.toNat - trimA.index ≤
                                  trimB.index
                              · simp [hlo,
                                mirrorMergeAtPreparation,
                                mirrorMergeAtCall,
                                mirrorMergeState, call]
                              · simp [hlo,
                                mirrorMergeAtPreparation,
                                mirrorMergeAtCall,
                                mirrorMergeState, call]
        · rw [if_neg hgeometry, if_neg hgeometry]
          rfl
  · simp [hposition]

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[prepareMergeAt?_key_compare_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
it never replaces the comparator.  This raw frame lemma is what lets the
explicit comparator premise flow into the selected merge continuation. -/
lemma prepareMergeAt?_key_compare_of_eq_some
  (state : MergeState (Occurrence alpha) nu) (i : Nat)
  (preparation : MergeAtPreparation (Occurrence alpha) nu)
  (hresult : prepareMergeAt? state i = some preparation) :
  preparation.state.key_compare = state.key_compare := by
  unfold prepareMergeAt? at hresult
  by_cases hposition :
    2 ≤ state.pending.size ∧
      (i + 2 = state.pending.size ∨ i + 3 = state.pending.size)
  · rw [if_pos hposition] at hresult
    cases hleft : state.pending[i]? with
    | none => simp [hleft] at hresult
    | some left =>
      simp only [hleft, mergeAt_bindOptionAcross_some] at hresult
      cases hright : state.pending[i + 1]? with
      | none => simp [hright] at hresult
      | some right =>
        simp only [hright, mergeAt_bindOptionAcross_some] at hresult
        by_cases hgeometry :
          (0 : PySSize).slt left.len ∧
            (0 : PySSize).slt right.len ∧
            left.base + left.len.toNat = right.base
        · rw [if_pos hgeometry] at hresult
          simp only [combinePendingAt_eq] at hresult
          let call : MergeState (Occurrence alpha) nu :=
            { state with
              pending :=
                (state.pending.setIfInBounds i
                  { left with len := left.len + right.len }).eraseIdxIfInBounds
                    (i + 1) }
          have hcallEq :
            ({ state with
              pending :=
                (state.pending.setIfInBounds i
                  { left with len := left.len + right.len }).eraseIdxIfInBounds
                    (i + 1) } : MergeState (Occurrence alpha) nu) = call :=
            rfl
          simp only [hcallEq] at hresult
          cases hfirst : state.data.read? (Int.ofNat right.base) with
          | none =>
            rw [hfirst] at hresult
            simp at hresult
          | some firstB =>
            rw [hfirst] at hresult
            simp only at hresult
            cases htrimA : gallopRight? call state.data
              (Int.ofNat left.base) firstB.key left.len.toNat 0 with
            | none =>
              rw [htrimA] at hresult
              simp at hresult
            | some trimA =>
              rw [htrimA] at hresult
              simp only [mergeAt_bindOptionAcross_some] at hresult
              by_cases htrimAFuel : trimA.fuelExhausted
              · rw [if_pos htrimAFuel] at hresult
                simp at hresult
                subst preparation
                rfl
              · rw [if_neg htrimAFuel] at hresult
                by_cases htrimABounds : left.len.toNat < trimA.index
                · simp [htrimABounds] at hresult
                · rw [if_neg htrimABounds] at hresult
                  by_cases hemptyA : left.len.toNat - trimA.index = 0
                  · rw [if_pos hemptyA] at hresult
                    simp at hresult
                    subst preparation
                    rfl
                  · rw [if_neg hemptyA] at hresult
                    cases hlast : state.data.read?
                      (Int.ofNat
                        (left.base + trimA.index +
                          (left.len.toNat - trimA.index) - 1)) with
                    | none =>
                      rw [hlast] at hresult
                      simp at hresult
                    | some lastA =>
                      rw [hlast] at hresult
                      simp only at hresult
                      cases htrimB : gallopLeft? call state.data
                        (Int.ofNat right.base) lastA.key
                        right.len.toNat (right.len.toNat - 1) with
                      | none =>
                        rw [htrimB] at hresult
                        simp at hresult
                      | some trimB =>
                        rw [htrimB] at hresult
                        simp only [mergeAt_bindOptionAcross_some]
                          at hresult
                        by_cases htrimBFuel : trimB.fuelExhausted
                        · rw [if_pos htrimBFuel] at hresult
                          simp at hresult
                          subst preparation
                          rfl
                        · rw [if_neg htrimBFuel] at hresult
                          by_cases htrimBBounds :
                            right.len.toNat < trimB.index
                          · simp [htrimBBounds] at hresult
                          · rw [if_neg htrimBBounds] at hresult
                            by_cases hemptyB : trimB.index = 0
                            · rw [if_pos hemptyB] at hresult
                              simp at hresult
                              subst preparation
                              rfl
                            · rw [if_neg hemptyB] at hresult
                              split at hresult <;>
                                simp at hresult <;>
                                subst preparation <;> rfl
        · rw [if_neg hgeometry] at hresult
          simp at hresult
  · simp [hposition] at hresult

end CPythonListsort

namespace CPythonListsort

/--
[mirrorFinishMergeAtPreparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma mirrorFinishMergeAtPreparation
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {size : Nat}
  {preparation : MergeAtPreparation (Occurrence alpha) nu}
-- given
  (hcompare : preparation.state.key_compare = occurrenceComparator lt) :
-- imply
  finishMergeAtPreparation? (mirrorMergeAtPreparation size preparation) = (finishMergeAtPreparation? preparation).map (mirrorMergeAtResult size) := by
-- proof
  cases preparation with
  | finished result => rfl
  | mergeLo call =>
    simp only [mirrorMergeAtPreparation, finishMergeAtPreparation?,
      mirrorMergeAtCall_state, mirrorMergeAtCall_ssa,
      mirrorMergeAtCall_ssb, mirrorMergeAtCall_na, mirrorMergeAtCall_nb]
    rw [mirrorMergeLo lt size call.state call.ssa call.ssb call.na call.nb
      hcompare]
    cases hmerge : mergeLo? call.state call.ssa call.ssb call.na call.nb with
    | none => rfl
    | some result =>
      simp [mirrorMergeAtResult, mirrorMergeLoResult]
  | mergeHi call =>
    simp only [mirrorMergeAtPreparation, finishMergeAtPreparation?,
      mirrorMergeAtCall_state, mirrorMergeAtCall_ssa,
      mirrorMergeAtCall_ssb, mirrorMergeAtCall_na, mirrorMergeAtCall_nb]
    rw [mirrorMergeHi lt size call.state call.ssa call.ssb call.na call.nb
      hcompare]
    cases hmerge : mergeHi? call.state call.ssa call.ssb call.na call.nb with
    | none => rfl
    | some result =>
      simp [mirrorMergeAtResult, mirrorMergeHiResult]

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[finishMergeAtPreparation?_key_compare_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
input preparation. -/
lemma finishMergeAtPreparation?_key_compare_of_eq_some
  (preparation : MergeAtPreparation (Occurrence alpha) nu)
  (result : MergeAtResult (Occurrence alpha) nu)
  (hresult : finishMergeAtPreparation? preparation = some result) :
  result.state.key_compare = preparation.state.key_compare := by
  cases preparation with
  | finished prepared =>
    simp only [finishMergeAtPreparation?, Option.some.injEq] at hresult
    subst result
    rfl
  | mergeLo call =>
    simp only [finishMergeAtPreparation?] at hresult
    cases hmerge : mergeLo? call.state call.ssa call.ssb call.na call.nb with
    | none => simp [hmerge] at hresult
    | some merged =>
      simp [hmerge] at hresult
      subst result
      simpa only [MergeAtPreparation.state] using
        (mergeLo?_key_compare_of_eq_some hmerge)
  | mergeHi call =>
    simp only [finishMergeAtPreparation?] at hresult
    cases hmerge : mergeHi? call.state call.ssa call.ssb call.na call.nb with
    | none => simp [hmerge] at hresult
    | some merged =>
      simp [hmerge] at hresult
      subst result
      simpa only [MergeAtPreparation.state] using
        (mergeHi?_key_compare_of_eq_some hmerge)

end CPythonListsort

namespace CPythonListsort

/--
[mirrorMergeAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma mirrorMergeAt
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {i : Nat}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  mergeAt? (mirrorMergeState size state) i = (mergeAt? state i).map (mirrorMergeAtResult size) := by
-- proof
  unfold mergeAt?
  rw [mirrorPrepareMergeAt lt size state i hcompare]
  cases hprepare : prepareMergeAt? state i with
  | none => rfl
  | some preparation =>
    simp only [Option.map_some, mergeAt_bindOptionAcross_some]
    apply mirrorFinishMergeAtPreparation lt size preparation
    rwa [prepareMergeAt?_key_compare_of_eq_some state i preparation hprepare]

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[mergeAt?_key_compare_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma mergeAt?_key_compare_of_eq_some
  (state : MergeState (Occurrence alpha) nu) (i : Nat)
  (result : MergeAtResult (Occurrence alpha) nu)
  (hresult : mergeAt? state i = some result) :
  result.state.key_compare = state.key_compare := by
  unfold mergeAt? at hresult
  cases hprepare : prepareMergeAt? state i with
  | none => simp [hprepare] at hresult
  | some preparation =>
    have hpreFrame :=
      prepareMergeAt?_key_compare_of_eq_some state i preparation hprepare
    have hfinish :=
      finishMergeAtPreparation?_key_compare_of_eq_some preparation result
        (by simpa [hprepare] using hresult)
    exact hfinish.trans hpreFrame

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[setTopPower?_key_compare_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma setTopPower?_key_compare_of_eq_some
  (state updated : MergeState (Occurrence alpha) nu) (power : Nat)
  (hresult : setTopPower? state power = some updated) :
  updated.key_compare = state.key_compare := by
  unfold setTopPower? at hresult
  split at hresult <;> simp_all
  split at hresult <;> simp_all
  subst updated
  rfl

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[foundNewRunLoop?_key_compare_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma foundNewRunLoop?_key_compare_of_eq_some
  (fuel : Nat) (state : MergeState (Occurrence alpha) nu) (power : Nat)
  (result : FoundNewRunResult (Occurrence alpha) nu)
  (hresult : foundNewRunLoop? fuel state power = some result) :
  result.state.key_compare = state.key_compare := by
  induction fuel generalizing state with
  | zero =>
    simp [foundNewRunLoop?, foundNewRunOutOfFuel_eq] at hresult
    subst result
    rfl
  | succ fuel ih =>
    simp only [foundNewRunLoop?] at hresult
    by_cases hdepth : 1 < state.pending.size
    · rw [if_pos hdepth] at hresult
      cases hpreceding : state.pending[state.pending.size - 2]? with
      | none => simp [hpreceding] at hresult
      | some preceding =>
        simp only [hpreceding] at hresult
        cases hpower : preceding.power with
        | none => simp [hpower] at hresult
        | some precedingPower =>
          simp only [hpower] at hresult
          by_cases hcollapse : power < precedingPower
          · rw [if_pos hcollapse] at hresult
            cases hmerge : mergeAt? state (state.pending.size - 2) with
            | none => simp [hmerge] at hresult
            | some merged =>
              simp only [hmerge] at hresult
              by_cases hok :
                merged.returnCode = 0 ∧ !merged.fuelExhausted
              · rw [if_pos hok] at hresult
                exact (ih merged.state hresult).trans
                  (mergeAt?_key_compare_of_eq_some state
                    (state.pending.size - 2) merged hmerge)
              · rw [if_neg hok] at hresult
                simp only [foundNewRunFromMergeAt_eq,
                  Option.some.injEq] at hresult
                subst result
                exact mergeAt?_key_compare_of_eq_some state
                  (state.pending.size - 2) merged hmerge
          · rw [if_neg hcollapse] at hresult
            cases hset : setTopPower? state power with
            | none => simp [hset] at hresult
            | some updated =>
              simp only [hset, foundNewRunSuccess_eq,
                Option.some.injEq] at hresult
              subst result
              exact setTopPower?_key_compare_of_eq_some state updated
                power hset
    · rw [if_neg hdepth] at hresult
      cases hset : setTopPower? state power with
      | none => simp [hset] at hresult
      | some updated =>
        simp only [hset, foundNewRunSuccess_eq,
          Option.some.injEq] at hresult
        subst result
        exact setTopPower?_key_compare_of_eq_some state updated power hset

end CPythonListsort

namespace CPythonListsort

/--
[mirrorFoundNewRunLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma mirrorFoundNewRunLoop
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {size fuel : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {power : Nat}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  foundNewRunLoop? fuel (mirrorMergeState size state) power = (foundNewRunLoop? fuel state power).map (mirrorFoundNewRunResult size) := by
-- proof
  induction fuel generalizing state with
  | zero =>
    simp [foundNewRunLoop?, foundNewRunOutOfFuel_eq,
      mirrorFoundNewRunResult, mirrorMergeState]
  | succ fuel ih =>
    simp only [mirrorMergeState]
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
            have hmirrorMerge := mirrorMergeAt lt size state
              (state.pending.size - 2) hcompare
            simp only [mirrorMergeState] at hmirrorMerge
            rw [hmirrorMerge]
            cases hmerge : mergeAt? state (state.pending.size - 2) with
            | none => simp
            | some merged =>
              simp only [Option.map_some,
                mirrorMergeAtResult_returnCode,
                mirrorMergeAtResult_fuelExhausted]
              simp only [mirrorMergeAtResult]
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
                  mirrorFoundNewRunResult]
          · rw [if_neg hcollapse, if_neg hcollapse]
            have hmirrorSet := mirrorSetTopPower size power state
            simp only [mirrorMergeState] at hmirrorSet
            rw [hmirrorSet]
            cases hset : setTopPower? state power with
            | none => simp
            | some updated =>
              simp [foundNewRunSuccess_eq,
                mirrorFoundNewRunResult]
    · rw [if_neg hdepth, if_neg hdepth]
      have hmirrorSet := mirrorSetTopPower size power state
      simp only [mirrorMergeState] at hmirrorSet
      rw [hmirrorSet]
      cases hset : setTopPower? state power with
      | none => simp
      | some updated =>
        simp [foundNewRunSuccess_eq, mirrorFoundNewRunResult]

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[foundNewRun?_key_compare_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma foundNewRun?_key_compare_of_eq_some
  (state : MergeState (Occurrence alpha) nu) (n2 : Nat)
  (result : FoundNewRunResult (Occurrence alpha) nu)
  (hresult : foundNewRun? state n2 = some result) :
  result.state.key_compare = state.key_compare := by
  unfold foundNewRun? at hresult
  by_cases hempty : state.pending.isEmpty
  · rw [if_pos hempty] at hresult
    simp [foundNewRunSuccess_eq] at hresult
    subst result
    rfl
  · rw [if_neg hempty] at hresult
    cases htop : state.pending[state.pending.size - 1]? with
    | none => simp [htop] at hresult
    | some top =>
      simp only [htop] at hresult
      split at hresult
      · split at hresult
        · simp [foundNewRunOutOfFuel_eq] at hresult
          subst result
          rfl
        · exact foundNewRunLoop?_key_compare_of_eq_some _ _ _ _ hresult
      · simp_all

end CPythonListsort

namespace CPythonListsort

/--
[mirrorFoundNewRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma mirrorFoundNewRun
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {n2 : Nat}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  foundNewRun? (mirrorMergeState size state) n2 = (foundNewRun? state n2).map (mirrorFoundNewRunResult size) := by
-- proof
  simp only [mirrorMergeState]
  unfold foundNewRun?
  by_cases hempty : state.pending.isEmpty
  · simp [hempty, foundNewRunSuccess_eq, mirrorFoundNewRunResult,
    mirrorMergeState]
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
          mirrorFoundNewRunResult, mirrorMergeState]
        · rw [if_neg hstopped, if_neg hstopped]
          have hloop := mirrorFoundNewRunLoop lt size state.pending.size state
            traced.result hcompare
          simpa [traced, mirrorMergeState] using hloop
      · rename_i hguard
        simp only [Option.map_none]

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[mergeForceCollapseLoop?_key_compare_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma mergeForceCollapseLoop?_key_compare_of_eq_some
  (fuel : Nat) (state : MergeState (Occurrence alpha) nu)
  (result : MergeForceCollapseResult (Occurrence alpha) nu)
  (hresult : mergeForceCollapseLoop? fuel state = some result) :
  result.state.key_compare = state.key_compare := by
  induction fuel generalizing state with
  | zero =>
    simp only [mergeForceCollapseLoop?] at hresult
    split at hresult <;>
      simp at hresult <;>
      subst result <;> rfl
  | succ fuel ih =>
    simp only [mergeForceCollapseLoop?] at hresult
    by_cases hdepth : 1 < state.pending.size
    · rw [if_pos hdepth] at hresult
      cases hindex : forceCollapseIndex? state with
      | none => simp [hindex] at hresult
      | some i =>
        simp only [hindex] at hresult
        cases hmerge : mergeAt? state i with
        | none => simp [hmerge] at hresult
        | some merged =>
          simp only [hmerge] at hresult
          by_cases hok :
            merged.returnCode = 0 ∧ !merged.fuelExhausted
          · rw [if_pos hok] at hresult
            exact (ih merged.state hresult).trans
              (mergeAt?_key_compare_of_eq_some state i merged hmerge)
          · rw [if_neg hok] at hresult
            simp only [Option.some.injEq] at hresult
            subst result
            exact mergeAt?_key_compare_of_eq_some state i merged hmerge
    · rw [if_neg hdepth] at hresult
      simp at hresult
      subst result
      rfl

end CPythonListsort

namespace CPythonListsort

/--
[mirrorMergeForceCollapseLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma mirrorMergeForceCollapseLoop
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {size fuel : Nat}
  {state : MergeState (Occurrence alpha) nu}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  mergeForceCollapseLoop? fuel (mirrorMergeState size state) = (mergeForceCollapseLoop? fuel state).map (mirrorMergeForceCollapseResult size) := by
-- proof
  induction fuel generalizing state with
  | zero =>
    simp only [mirrorMergeState]
    simp only [mergeForceCollapseLoop?]
    split <;> rfl
  | succ fuel ih =>
    simp only [mirrorMergeState]
    simp only [mergeForceCollapseLoop?]
    by_cases hdepth : 1 < state.pending.size
    · rw [if_pos hdepth, if_pos hdepth]
      have hmirrorIndex := mirrorForceCollapseIndex size state
      simp only [mirrorMergeState] at hmirrorIndex
      rw [hmirrorIndex]
      cases hindex : forceCollapseIndex? state with
      | none => simp
      | some i =>
        simp only
        have hmirrorMerge := mirrorMergeAt lt size state i hcompare
        simp only [mirrorMergeState] at hmirrorMerge
        rw [hmirrorMerge]
        cases hmerge : mergeAt? state i with
        | none => simp
        | some merged =>
          simp only [Option.map_some,
            mirrorMergeAtResult_returnCode,
            mirrorMergeAtResult_fuelExhausted]
          simp only [mirrorMergeAtResult]
          split
          · rename_i hok
            simp only [hok]
            apply ih
            exact
              (mergeAt?_key_compare_of_eq_some state i merged hmerge).trans
                hcompare
          · rename_i hok
            simp only [hok, if_false]
            rfl
    · rw [if_neg hdepth, if_neg hdepth]
      rfl

end CPythonListsort

namespace CPythonListsort

/--
[mirrorMergeForceCollapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma mirrorMergeForceCollapse
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  mergeForceCollapse? (mirrorMergeState size state) = (mergeForceCollapse? state).map (mirrorMergeForceCollapseResult size) := by
-- proof
  unfold mergeForceCollapse?
  rw [mirrorMergeState_pending]
  exact mirrorMergeForceCollapseLoop lt size state.pending.size state hcompare

end CPythonListsort

namespace CPythonListsort

/--
[mirrorFinishListSort](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma mirrorFinishListSort
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {reverse : Bool}
  {inputSize : Nat}
  {returnCode : Int}
  {fuelExhausted : Bool} :
-- imply
  finishListSort? (mirrorMergeState size state) reverse inputSize returnCode fuelExhausted = (finishListSort? state reverse inputSize returnCode fuelExhausted).map (mirrorListSortImplResult size) := by
-- proof
  unfold finishListSort?
  by_cases hreverse : reverse && decide (1 < inputSize)
  · rw [if_pos hreverse, if_pos hreverse]
    simp only [mirrorMergeState_data]
    rw [mirrorSortsliceReverse]
    cases hreversed : sortsliceReverse? state.data 0 inputSize with
    | none => simp
    | some reversed =>
      simp only [Option.map_some, bind, Option.bind,
        mirrorReverseSliceResult]
      rw [mirrorMergeState_setData, mirrorMergeFreemem]
      rfl
  · rw [if_neg hreverse, if_neg hreverse]
    simp only [bind, Option.bind]
    rw [mirrorMergeFreemem]
    rfl

end CPythonListsort

namespace CPythonListsort

/--
[mirrorFailFromFoundNewRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma mirrorFailFromFoundNewRun
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : FoundNewRunResult (Occurrence alpha) nu}
  {reverse : Bool}
  {inputSize : Nat} :
-- imply
  failFromFoundNewRun? (mirrorFoundNewRunResult size result) reverse inputSize = (failFromFoundNewRun? result reverse inputSize).map (mirrorListSortImplResult size) := by
-- proof
  simp [failFromFoundNewRun?]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorFailFromCollapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma mirrorFailFromCollapse
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : MergeForceCollapseResult (Occurrence alpha) nu}
  {reverse : Bool}
  {inputSize : Nat} :
-- imply
  failFromCollapse? (mirrorMergeForceCollapseResult size result) reverse inputSize = (failFromCollapse? result reverse inputSize).map (mirrorListSortImplResult size) := by
-- proof
  simp [failFromCollapse?]

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[mirrorListSortScanAfterExtension](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
assuming the recursive scan call itself commutes. -/
private lemma mirrorListSortScanAfterExtension
  (lt : BoolComparator alpha) (size fuel : Nat)
  (state : MergeState (Occurrence alpha) nu) (lo remaining : Nat)
  (reverse : Bool) (inputSize runLength : Nat) (extensionFuel : Bool)
  (hcompare : state.key_compare = occurrenceComparator lt)
  (hscan : ∀ (nextState : MergeState (Occurrence alpha) nu)
    (nextLo nextRemaining : Nat),
    nextState.key_compare = occurrenceComparator lt →
      listSortScan? fuel (mirrorMergeState size nextState) nextLo
        nextRemaining reverse inputSize =
        (listSortScan? fuel nextState nextLo nextRemaining reverse
          inputSize).map (mirrorListSortImplResult size)) :
  listSortScanAfterExtension? fuel (mirrorMergeState size state) lo
    remaining reverse inputSize runLength extensionFuel =
    (listSortScanAfterExtension? fuel state lo remaining reverse inputSize
      runLength extensionFuel).map (mirrorListSortImplResult size) := by
  unfold listSortScanAfterExtension?
  by_cases hextFuel : extensionFuel
  · rw [if_pos hextFuel, if_pos hextFuel]
    exact mirrorFinishListSort size state reverse inputSize (-1) true
  · rw [if_neg hextFuel, if_neg hextFuel]
    by_cases hbad : runLength = 0 ∨ remaining < runLength
    · simp [hbad]
    · rw [if_neg hbad, if_neg hbad]
      rw [mirrorFoundNewRun lt size state runLength hcompare]
      cases hfound : foundNewRun? state runLength with
      | none => simp
      | some found =>
        simp only [Option.map_some,
          mirrorFoundNewRunResult_returnCode,
          mirrorFoundNewRunResult_fuelExhausted]
        simp only [mirrorFoundNewRunResult]
        split
        · rename_i hok
          simp only [hok, mirrorPushPendingRun]
          apply hscan
          exact
            (foundNewRun?_key_compare_of_eq_some state runLength found
              hfound).trans hcompare
        · rename_i hok
          simp only [hok, if_false]
          exact mirrorFailFromFoundNewRun size found reverse inputSize

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[mirrorListSortScanAfterCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
`countRun?`, assuming the recursive scan call itself commutes. -/
private lemma mirrorListSortScanAfterCount
  (lt : BoolComparator alpha) (size fuel : Nat)
  (state : MergeState (Occurrence alpha) nu) (lo remaining : Nat)
  (reverse : Bool) (inputSize : Nat)
  (counted : CountRunResult (Occurrence alpha) nu)
  (hcompare : state.key_compare = occurrenceComparator lt)
  (hscan : ∀ (nextState : MergeState (Occurrence alpha) nu)
    (nextLo nextRemaining : Nat),
    nextState.key_compare = occurrenceComparator lt →
      listSortScan? fuel (mirrorMergeState size nextState) nextLo
        nextRemaining reverse inputSize =
        (listSortScan? fuel nextState nextLo nextRemaining reverse
          inputSize).map (mirrorListSortImplResult size)) :
  listSortScanAfterCount? fuel (mirrorMergeState size state) lo remaining
    reverse inputSize (mirrorCountRunResult size counted) =
    (listSortScanAfterCount? fuel state lo remaining reverse inputSize
      counted).map (mirrorListSortImplResult size) := by
  unfold listSortScanAfterCount?
  simp only [mirrorCountRunResult_slice, mirrorCountRunResult_length,
    mirrorCountRunResult_fuel, mirrorMergeState_setData]
  set countedState : MergeState (Occurrence alpha) nu :=
    { state with data := counted.slice }
  have hcountedCompare :
    countedState.key_compare = occurrenceComparator lt := hcompare
  by_cases hcountFuel : counted.fuelExhausted
  · rw [if_pos hcountFuel, if_pos hcountFuel]
    exact mirrorFinishListSort size countedState reverse inputSize (-1) true
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
        have hextendMirror :
          (BitVec.ofNat 64 counted.length : PySSize).slt
            (minrunNext (mirrorMergeState size countedState).minrunState).result := by
          simpa only [mirrorMergeState_minrunState] using hextendBase
        rw [if_pos hextendMirror, if_pos hextendBase]
        by_cases hforce : remaining ≤ target
        · have hforceBase :
          remaining ≤ (minrunNext countedState.minrunState).result.toNat := by
          simpa only [target, nextMinrun] using hforce
          have hforceMirror :
            remaining ≤ (minrunNext
              (mirrorMergeState size countedState).minrunState).result.toNat := by
            simpa only [mirrorMergeState_minrunState] using hforceBase
          simp only [if_pos hforceMirror, if_pos hforceBase]
          simp only [mirrorMergeState_minrunState, mirrorInstallMinrunState,
            mirrorMergeState_data]
          rw [mirrorBinarysort lt size nextState nextState.data (Int.ofNat lo)
            remaining runLength hnextCompare]
          cases hsorted : binarysort? nextState nextState.data (Int.ofNat lo)
            remaining runLength with
          | none => simp
          | some sorted =>
            simp only [Option.map_some, bind, Option.bind,
              mirrorBinarysortResult_slice, mirrorBinarysortResult_fuel,
              mirrorMergeState_setData]
            exact mirrorListSortScanAfterExtension lt size fuel
              { nextState with data := sorted.slice } lo remaining reverse
              inputSize remaining sorted.fuelExhausted hnextCompare hscan
        · have hforceBase :
          ¬ remaining ≤ (minrunNext countedState.minrunState).result.toNat := by
          simpa only [target, nextMinrun] using hforce
          have hforceMirror :
            ¬ remaining ≤ (minrunNext
              (mirrorMergeState size countedState).minrunState).result.toNat := by
            simpa only [mirrorMergeState_minrunState] using hforceBase
          simp only [if_neg hforceMirror, if_neg hforceBase]
          simp only [mirrorMergeState_minrunState, mirrorInstallMinrunState,
            mirrorMergeState_data]
          rw [mirrorBinarysort lt size nextState nextState.data (Int.ofNat lo)
            target runLength hnextCompare]
          cases hsorted : binarysort? nextState nextState.data (Int.ofNat lo)
            target runLength with
          | none => simp
          | some sorted =>
            simp only [Option.map_some, bind, Option.bind,
              mirrorBinarysortResult_slice, mirrorBinarysortResult_fuel,
              mirrorMergeState_setData]
            exact mirrorListSortScanAfterExtension lt size fuel
              { nextState with data := sorted.slice } lo remaining reverse
              inputSize target sorted.fuelExhausted hnextCompare hscan
      · have hextendBase :
        ¬ (BitVec.ofNat 64 counted.length : PySSize).slt
          (minrunNext countedState.minrunState).result := by
        simpa only [runLength, nextMinrun] using hextend
        have hextendMirror :
          ¬ (BitVec.ofNat 64 counted.length : PySSize).slt
            (minrunNext (mirrorMergeState size countedState).minrunState).result := by
          simpa only [mirrorMergeState_minrunState] using hextendBase
        rw [if_neg hextendMirror, if_neg hextendBase]
        simp only [mirrorMergeState_minrunState, mirrorInstallMinrunState,
          mirrorMergeState_data, bind, Option.bind, mirrorMergeState_setData]
        exact mirrorListSortScanAfterExtension lt size fuel
          { nextState with data := nextState.data } lo remaining reverse
          inputSize runLength false hnextCompare hscan

end CPythonListsort

namespace CPythonListsort

variable {alpha : Type u} {nu : Type v}
/--
[listSortScan_succ_of_remaining_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma listSortScan_succ_of_remaining_ne_zero
  (fuel : Nat) (state : MergeState (Occurrence alpha) nu)
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
      let countedState : MergeState (Occurrence alpha) nu :=
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
              MergeState (Occurrence alpha) nu).minrunState).result := by
        simpa only [runLength, nextMinrun, countedState] using hextend
        simp only [hextendBase, if_true]
        by_cases hforce : remaining ≤ target
        · have hforceBase :
          remaining ≤
            (minrunNext
              ({ state with data := counted.slice } :
                MergeState (Occurrence alpha) nu).minrunState).result.toNat := by
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
                MergeState (Occurrence alpha) nu).minrunState).result.toNat := by
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
              MergeState (Occurrence alpha) nu).minrunState).result := by
        simpa only [runLength, nextMinrun, countedState] using hextend
        simp [hextendBase, hcountBad]
        split <;> simp_all

end CPythonListsort

namespace CPythonListsort

/--
[mirrorListSortScan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
lemma mirrorListSortScan
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {size fuel : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {lo remaining : Nat}
  {reverse : Bool}
  {inputSize : Nat}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  listSortScan? fuel (mirrorMergeState size state) lo remaining reverse inputSize = (listSortScan? fuel state lo remaining reverse inputSize).map (mirrorListSortImplResult size) := by
-- proof
  induction fuel generalizing state lo remaining with
  | zero =>
    simp only [listSortScan?]
    by_cases hremaining : remaining = 0
    · rw [if_pos hremaining, if_pos hremaining]
      have hmirrorCollapse :=
        mirrorMergeForceCollapse lt size state hcompare
      rw [hmirrorCollapse]
      cases hcollapse : mergeForceCollapse? state with
      | none => simp
      | some collapsed =>
        simp only [Option.map_some,
          mirrorMergeForceCollapseResult_returnCode,
          mirrorMergeForceCollapseResult_fuelExhausted]
        simp only [mirrorMergeForceCollapseResult]
        split
        · rename_i hok
          simp only [hok]
          exact mirrorFinishListSort size collapsed.state reverse
            inputSize 0 false
        · rename_i hok
          simp only [hok, if_false]
          exact mirrorFailFromCollapse size collapsed reverse inputSize
    · rw [if_neg hremaining, if_neg hremaining]
      exact mirrorFinishListSort size state reverse inputSize (-1) true
  | succ fuel ih =>
    by_cases hremaining : remaining = 0
    · simp only [listSortScan?]
      rw [if_pos hremaining, if_pos hremaining]
      have hmirrorCollapse :=
        mirrorMergeForceCollapse lt size state hcompare
      rw [hmirrorCollapse]
      cases hcollapse : mergeForceCollapse? state with
      | none => simp
      | some collapsed =>
        simp only [Option.map_some,
          mirrorMergeForceCollapseResult_returnCode,
          mirrorMergeForceCollapseResult_fuelExhausted]
        simp only [mirrorMergeForceCollapseResult]
        split
        · rename_i hok
          simp only [hok]
          exact mirrorFinishListSort size collapsed.state reverse
            inputSize 0 false
        · rename_i hok
          simp only [hok, if_false]
          exact mirrorFailFromCollapse size collapsed reverse inputSize
    · have hmirrorStep :=
      listSortScan_succ_of_remaining_ne_zero fuel
        (mirrorMergeState size state) lo remaining reverse inputSize
        hremaining
      have hbaseStep :=
        listSortScan_succ_of_remaining_ne_zero fuel state lo remaining
          reverse inputSize hremaining
      rw [hmirrorStep, hbaseStep]
      have hmirrorCount := mirrorCountRun lt size state state.data
        (Int.ofNat lo) remaining hcompare
      rw [mirrorMergeState_data]
      rw [hmirrorCount]
      cases hcount : countRun? state state.data (Int.ofNat lo) remaining with
      | none => simp
      | some counted =>
        simp only [Option.map_some, bind, Option.bind]
        have htail := mirrorListSortScanAfterCount lt size fuel state lo
          remaining reverse inputSize counted hcompare
          (fun nextState nextLo nextRemaining hnextCompare =>
            ih nextState nextLo nextRemaining hnextCompare)
        exact htail

end CPythonListsort

/--
[mirrorMergeAtResult_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorMergeAtResult_state_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : MergeAtResult (Occurrence alpha) nu} :
-- imply
  (mirrorMergeAtResult size result).state = mirrorMergeState size result.state := by
-- proof
  apply CPythonListsort.mirrorMergeAtResult_state size result

/--
[mirrorMergeAtResult_returnCode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorMergeAtResult_returnCode_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : MergeAtResult (Occurrence alpha) nu} :
-- imply
  (mirrorMergeAtResult size result).returnCode = result.returnCode := by
-- proof
  apply CPythonListsort.mirrorMergeAtResult_returnCode size result

/--
[mirrorMergeAtResult_fuelExhausted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorMergeAtResult_fuelExhausted_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : MergeAtResult (Occurrence alpha) nu} :
-- imply
  (mirrorMergeAtResult size result).fuelExhausted = result.fuelExhausted := by
-- proof
  apply CPythonListsort.mirrorMergeAtResult_fuelExhausted size result

/--
[mirrorMergeAtCall_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorMergeAtCall_state_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {call : MergeAtCall (Occurrence alpha) nu} :
-- imply
  (mirrorMergeAtCall size call).state = mirrorMergeState size call.state := by
-- proof
  apply CPythonListsort.mirrorMergeAtCall_state size call

/--
[mirrorMergeAtCall_firstB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorMergeAtCall_firstB_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {call : MergeAtCall (Occurrence alpha) nu} :
-- imply
  (mirrorMergeAtCall size call).firstB = mirrorSortSliceEntry size call.firstB := by
-- proof
  apply CPythonListsort.mirrorMergeAtCall_firstB size call

/--
[mirrorMergeAtCall_lastA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorMergeAtCall_lastA_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {call : MergeAtCall (Occurrence alpha) nu} :
-- imply
  (mirrorMergeAtCall size call).lastA = mirrorSortSliceEntry size call.lastA := by
-- proof
  apply CPythonListsort.mirrorMergeAtCall_lastA size call

/--
[mirrorMergeAtCall_ssa](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorMergeAtCall_ssa_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {call : MergeAtCall (Occurrence alpha) nu} :
-- imply
  (mirrorMergeAtCall size call).ssa = call.ssa := by
-- proof
  apply CPythonListsort.mirrorMergeAtCall_ssa size call

/--
[mirrorMergeAtCall_ssb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorMergeAtCall_ssb_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {call : MergeAtCall (Occurrence alpha) nu} :
-- imply
  (mirrorMergeAtCall size call).ssb = call.ssb := by
-- proof
  apply CPythonListsort.mirrorMergeAtCall_ssb size call

/--
[mirrorMergeAtCall_na](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorMergeAtCall_na_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {call : MergeAtCall (Occurrence alpha) nu} :
-- imply
  (mirrorMergeAtCall size call).na = call.na := by
-- proof
  apply CPythonListsort.mirrorMergeAtCall_na size call

/--
[mirrorMergeAtCall_nb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorMergeAtCall_nb_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {call : MergeAtCall (Occurrence alpha) nu} :
-- imply
  (mirrorMergeAtCall size call).nb = call.nb := by
-- proof
  apply CPythonListsort.mirrorMergeAtCall_nb size call

/--
[mirrorMergeAtPreparation_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorMergeAtPreparation_state_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {preparation : MergeAtPreparation (Occurrence alpha) nu} :
-- imply
  (mirrorMergeAtPreparation size preparation).state = mirrorMergeState size preparation.state := by
-- proof
  apply CPythonListsort.mirrorMergeAtPreparation_state size preparation

/--
[mirrorFoundNewRunResult_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorFoundNewRunResult_state_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : FoundNewRunResult (Occurrence alpha) nu} :
-- imply
  (mirrorFoundNewRunResult size result).state = mirrorMergeState size result.state := by
-- proof
  apply CPythonListsort.mirrorFoundNewRunResult_state size result

/--
[mirrorFoundNewRunResult_returnCode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorFoundNewRunResult_returnCode_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : FoundNewRunResult (Occurrence alpha) nu} :
-- imply
  (mirrorFoundNewRunResult size result).returnCode = result.returnCode := by
-- proof
  apply CPythonListsort.mirrorFoundNewRunResult_returnCode size result

/--
[mirrorFoundNewRunResult_fuelExhausted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorFoundNewRunResult_fuelExhausted_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : FoundNewRunResult (Occurrence alpha) nu} :
-- imply
  (mirrorFoundNewRunResult size result).fuelExhausted = result.fuelExhausted := by
-- proof
  apply CPythonListsort.mirrorFoundNewRunResult_fuelExhausted size result

/--
[mirrorMergeForceCollapseResult_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorMergeForceCollapseResult_state_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : MergeForceCollapseResult (Occurrence alpha) nu} :
-- imply
  (mirrorMergeForceCollapseResult size result).state = mirrorMergeState size result.state := by
-- proof
  apply CPythonListsort.mirrorMergeForceCollapseResult_state size result

/--
[mirrorMergeForceCollapseResult_returnCode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorMergeForceCollapseResult_returnCode_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : MergeForceCollapseResult (Occurrence alpha) nu} :
-- imply
  (mirrorMergeForceCollapseResult size result).returnCode = result.returnCode := by
-- proof
  apply CPythonListsort.mirrorMergeForceCollapseResult_returnCode size result

/--
[mirrorMergeForceCollapseResult_fuelExhausted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorMergeForceCollapseResult_fuelExhausted_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : MergeForceCollapseResult (Occurrence alpha) nu} :
-- imply
  (mirrorMergeForceCollapseResult size result).fuelExhausted = result.fuelExhausted := by
-- proof
  apply CPythonListsort.mirrorMergeForceCollapseResult_fuelExhausted size result

/--
[mirrorListSortImplResult_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorListSortImplResult_state_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : ListSortImplResult (Occurrence alpha) nu} :
-- imply
  (mirrorListSortImplResult size result).state = mirrorMergeState size result.state := by
-- proof
  apply CPythonListsort.mirrorListSortImplResult_state size result

/--
[mirrorListSortImplResult_returnCode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorListSortImplResult_returnCode_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : ListSortImplResult (Occurrence alpha) nu} :
-- imply
  (mirrorListSortImplResult size result).returnCode = result.returnCode := by
-- proof
  apply CPythonListsort.mirrorListSortImplResult_returnCode size result

/--
[mirrorListSortImplResult_fuelExhausted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorListSortImplResult_fuelExhausted_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : ListSortImplResult (Occurrence alpha) nu} :
-- imply
  (mirrorListSortImplResult size result).fuelExhausted = result.fuelExhausted := by
-- proof
  apply CPythonListsort.mirrorListSortImplResult_fuelExhausted size result

/--
[mirrorMergeAtResult_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorMergeAtResult_involutive_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : MergeAtResult (Occurrence alpha) nu} :
-- imply
  mirrorMergeAtResult size (mirrorMergeAtResult size result) = result := by
-- proof
  apply CPythonListsort.mirrorMergeAtResult_involutive size result

/--
[mirrorMergeAtCall_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorMergeAtCall_involutive_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {call : MergeAtCall (Occurrence alpha) nu} :
-- imply
  mirrorMergeAtCall size (mirrorMergeAtCall size call) = call := by
-- proof
  apply CPythonListsort.mirrorMergeAtCall_involutive size call

/--
[mirrorMergeAtPreparation_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorMergeAtPreparation_involutive_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {preparation : MergeAtPreparation (Occurrence alpha) nu} :
-- imply
  mirrorMergeAtPreparation size (mirrorMergeAtPreparation size preparation) = preparation := by
-- proof
  apply CPythonListsort.mirrorMergeAtPreparation_involutive size preparation

/--
[mirrorFoundNewRunResult_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorFoundNewRunResult_involutive_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : FoundNewRunResult (Occurrence alpha) nu} :
-- imply
  mirrorFoundNewRunResult size (mirrorFoundNewRunResult size result) = result := by
-- proof
  apply CPythonListsort.mirrorFoundNewRunResult_involutive size result

/--
[mirrorMergeForceCollapseResult_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorMergeForceCollapseResult_involutive_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : MergeForceCollapseResult (Occurrence alpha) nu} :
-- imply
  mirrorMergeForceCollapseResult size (mirrorMergeForceCollapseResult size result) = result := by
-- proof
  apply CPythonListsort.mirrorMergeForceCollapseResult_involutive size result

/--
[mirrorListSortImplResult_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mirrorListSortImplResult_involutive_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : ListSortImplResult (Occurrence alpha) nu} :
-- imply
  mirrorListSortImplResult size (mirrorListSortImplResult size result) = result := by
-- proof
  apply CPythonListsort.mirrorListSortImplResult_involutive size result

/--
[prepareMergeAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma prepareMergeAt_eq
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu}
  {i : Nat}
  {preparation : MergeAtPreparation (Occurrence alpha) nu}
-- given
  (hresult : prepareMergeAt? state i = some preparation) :
-- imply
  preparation.state.key_compare = state.key_compare := by
-- proof
  apply CPythonListsort.prepareMergeAt state i preparation hresult

/--
[finishMergeAtPreparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma finishMergeAtPreparation_eq
  {alpha : Type u}
  {nu : Type v}
  {preparation : MergeAtPreparation (Occurrence alpha) nu}
  {result : MergeAtResult (Occurrence alpha) nu}
-- given
  (hresult : finishMergeAtPreparation? preparation = some result) :
-- imply
  result.state.key_compare = preparation.state.key_compare := by
-- proof
  apply CPythonListsort.finishMergeAtPreparation preparation result hresult

/--
[mergeAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mergeAt_eq
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu}
  {i : Nat}
  {result : MergeAtResult (Occurrence alpha) nu}
-- given
  (hresult : mergeAt? state i = some result) :
-- imply
  result.state.key_compare = state.key_compare := by
-- proof
  apply CPythonListsort.mergeAt state i result hresult

/--
[setTopPower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma setTopPower_eq
  {alpha : Type u}
  {nu : Type v}
  {state updated : MergeState (Occurrence alpha) nu}
  {power : Nat}
-- given
  (hresult : setTopPower? state power = some updated) :
-- imply
  updated.key_compare = state.key_compare := by
-- proof
  apply CPythonListsort.setTopPower state updated power hresult

/--
[foundNewRunLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma foundNewRunLoop_eq
  {alpha : Type u}
  {nu : Type v}
  {fuel : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {power : Nat}
  {result : FoundNewRunResult (Occurrence alpha) nu}
-- given
  (hresult : foundNewRunLoop? fuel state power = some result) :
-- imply
  result.state.key_compare = state.key_compare := by
-- proof
  apply CPythonListsort.foundNewRunLoop fuel state power result hresult

/--
[foundNewRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma foundNewRun_eq
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu}
  {n2 : Nat}
  {result : FoundNewRunResult (Occurrence alpha) nu}
-- given
  (hresult : foundNewRun? state n2 = some result) :
-- imply
  result.state.key_compare = state.key_compare := by
-- proof
  apply CPythonListsort.foundNewRun state n2 result hresult

/--
[mergeForceCollapseLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelScan.lean)
-/
@[path]
private lemma mergeForceCollapseLoop_eq
  {alpha : Type u}
  {nu : Type v}
  {fuel : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {result : MergeForceCollapseResult (Occurrence alpha) nu}
-- given
  (hresult : mergeForceCollapseLoop? fuel state = some result) :
-- imply
  result.state.key_compare = state.key_compare := by
-- proof
  apply CPythonListsort.mergeForceCollapseLoop fuel state result hresult


-- created on 2026-10-23

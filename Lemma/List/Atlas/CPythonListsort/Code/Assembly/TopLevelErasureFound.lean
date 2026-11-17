import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.CPythonListsort.Code.Assembly.FoundNewRunSafety.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.FoundNewRunSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.TopLevelErasure
open CPythonListsort


namespace CPythonListsort

/--
[erase_foundNewRunLoopTraced_of_mergeAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/TopLevelErasureFound.lean)
-/
@[path]
lemma erase_foundNewRunLoopTraced_of_mergeAt
  {κ : Type u}
  {ν : Type v}
-- given
  (hMergeAt : ∀ (state : MergeState κ ν) (i : Nat), (mergeAtTraced? state i).erase = mergeAt? state i) :
-- imply
  ∀ (fuel : Nat) (state : MergeState κ ν) (power : Nat), (foundNewRunLoopTraced? fuel state power).erase = foundNewRunLoop? fuel state power := by
-- proof
  intro fuel
  induction fuel with
  | zero =>
    intro state power
    simp [foundNewRunLoopTraced?, foundNewRunLoop?,
      TraceResult.erase_markFuelExhausted, foundNewRunOutOfFuel_eq]
    rfl
  | succ fuel ih =>
    intro state power
    simp only [foundNewRunLoopTraced?, foundNewRunLoop?]
    by_cases hmany : 1 < state.pending.size
    · rw [ite_eq_left hmany, ite_eq_left hmany, TraceResult.erase_bind,
      TraceResult.erase_pendingRunRead]
      have hnonnegative :
        0 ≤ Int.ofNat (state.pending.size - 2) := Int.natCast_nonneg _
      rw [ite_eq_left hnonnegative]
      have htoi :
        (Int.ofNat (state.pending.size - 2)).toNat =
          state.pending.size - 2 := rfl
      rw [htoi]
      cases hpreceding : state.pending[state.pending.size - 2]? with
      | none => simp
      | some preceding =>
        simp only [Option.bind_some]
        cases hpower : preceding.power with
        | none => simp
        | some precedingPower =>
          simp only
          by_cases hcollapse : power < precedingPower
          · rw [ite_eq_left hcollapse, ite_eq_left hcollapse,
            TraceResult.erase_bind, hMergeAt]
            cases hmerged : mergeAt? state (state.pending.size - 2) with
            | none => simp
            | some merged =>
              simp only [Option.bind_some]
              by_cases hsuccess :
                merged.returnCode = 0 ∧ !merged.fuelExhausted
              · rw [ite_eq_left hsuccess, ite_eq_left hsuccess]
                exact ih merged.state power
              · rw [ite_eq_right hsuccess, ite_eq_right hsuccess]
                rfl
          · rw [ite_eq_right hcollapse, ite_eq_right hcollapse,
            TraceResult.erase_map, erase_setTopPowerTraced]
            cases hset : setTopPower? state power with
            | none => simp
            | some after =>
              simp only [Option.map_some]
              rfl
    · rw [ite_eq_right hmany, ite_eq_right hmany, TraceResult.erase_map,
      erase_setTopPowerTraced]
      cases hset : setTopPower? state power with
      | none => simp
      | some after =>
        simp only [Option.map_some]
        rfl

end CPythonListsort

namespace CPythonListsort

/--
[erase_foundNewRunTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/TopLevelErasureFound.lean)
-/
@[path]
lemma erase_foundNewRunTraced
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {n2 : Nat} :
-- imply
  (foundNewRunTraced? state n2).erase = foundNewRun? state n2 := by
-- proof
  unfold foundNewRunTraced? foundNewRun?
  by_cases hempty : state.pending.isEmpty = true
  · rw [ite_eq_left hempty, ite_eq_left hempty]
    rfl
  · rw [ite_eq_right hempty, ite_eq_right hempty, TraceResult.erase_bind,
    TraceResult.erase_pendingRunRead]
    have hnonnegative :
      0 ≤ Int.ofNat (state.pending.size - 1) := Int.natCast_nonneg _
    rw [ite_eq_left hnonnegative]
    have htoi :
      (Int.ofNat (state.pending.size - 1)).toNat =
        state.pending.size - 1 := rfl
    rw [htoi]
    cases htop : state.pending[state.pending.size - 1]? with
    | none => simp
    | some top =>
      simp only [Option.bind_some]
      let guard :=
        ((!state.listlen.msb) && decide (state.basekeys ≤ top.base) &&
          (0 : PySSize).slt top.len && decide (0 < n2) &&
          decide (n2 ≤ PY_SSIZE_T_MAX) &&
          decide (top.base - state.basekeys + top.len.toNat + n2 ≤
            state.listlen.toNat))
      by_cases hguard : guard = true
      · have hguard' :
        ((!state.listlen.msb) && decide (state.basekeys ≤ top.base) &&
          (0 : PySSize).slt top.len && decide (0 < n2) &&
          decide (n2 ≤ PY_SSIZE_T_MAX) &&
          decide (top.base - state.basekeys + top.len.toNat + n2 ≤
            state.listlen.toNat)) = true := hguard
        simp only [hguard', ite_true]
        let powered := powerloopTraced
          (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
          (BitVec.ofNat 64 n2) state.listlen
        by_cases hstopped : (!powered.stopped) = true
        · have hstopped' :
          (!(powerloopTraced
            (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
            (BitVec.ofNat 64 n2) state.listlen).stopped) = true :=
          hstopped
          simp only [hstopped', ite_true]
          simp [TraceResult.erase_markFuelExhausted]
          rfl
        · have hstopped' : ¬
          (!(powerloopTraced
            (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
            (BitVec.ofNat 64 n2) state.listlen).stopped) = true :=
          hstopped
          simp only [hstopped']
          exact erase_foundNewRunLoopTraced_of_mergeAt erase_mergeAtTraced
            _ _ _
      · have hguard' : ¬
        ((!state.listlen.msb) && decide (state.basekeys ≤ top.base) &&
          (0 : PySSize).slt top.len && decide (0 < n2) &&
          decide (n2 ≤ PY_SSIZE_T_MAX) &&
          decide (top.base - state.basekeys + top.len.toNat + n2 ≤
            state.listlen.toNat)) = true := hguard
        simp only [hguard']
        rfl

end CPythonListsort


-- created on 2026-10-23

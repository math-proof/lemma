/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part9


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

theorem survivalExceptionalMirror_horizontal_run_left
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (w : SurvivalExceptionalMirrorFamily R start (level : Int)
      walkLength target) :
    isingLineChoiceRun level (leftGapNeighbor level hlevel)
        (horizontalLeftCode w.1.1.1.reflectPrefix.steps) =
      leftGapLeft level := by
  let split := w.1.1.1
  let path := split.reflectPrefix.steps
  have hrefValid : IsingDiagonalWalkStepsValid path :=
    reflectPrefix_valid split w.1.1.2.2.1
  rcases survivalExceptionalMirror_reflected_exists_hit_left R start
      (level : Int) walkLength target hstart (by exact_mod_cast hlevel) w with
    ⟨k, hkbefore, hhit⟩
  change k < split.before.length at hkbefore
  change (isingDiagonalWalkEndpoint start (path.take k)).1 = 0 at hhit
  have hkpath : k ≤ path.length := by
    dsimp [path]
    rw [reflectPrefix_length]
    unfold steps
    simp only [List.length_append]
    exact le_trans hkbefore.le (Nat.le_add_right _ _)
  have hfreeHit :
      lineFreeEndpoint ((level - 1 : Nat) : Int)
          ((horizontalLeftCode path).take k) = 0 := by
    have htakeValid : IsingDiagonalWalkStepsValid (path.take k) := by
      intro d hd
      exact hrefValid d (List.mem_of_mem_take hd)
    have hline := lineFreeEndpoint_horizontalLeftCode (path.take k) start
      htakeValid
    have hinitial : ((level - 1 : Nat) : Int) = start.1 := by
      push_cast
      omega
    have hline' : lineFreeEndpoint start.1
        ((horizontalLeftCode path).take k) =
          (isingDiagonalWalkEndpoint start (path.take k)).1 := by
      simpa only [horizontalLeftCode, List.map_take] using hline
    rw [← hinitial, hhit] at hline'
    exact hline'
  have hnoRight : ∀ j, j < k →
      lineFreeEndpoint ((level - 1 : Nat) : Int)
        ((horizontalLeftCode path).take j) ≠ (level : Nat) := by
    intro j hj hright
    have hjbefore : j < split.before.length := by omega
    have htakeValid : IsingDiagonalWalkStepsValid (path.take j) := by
      intro d hd
      exact hrefValid d (List.mem_of_mem_take hd)
    have hline := lineFreeEndpoint_horizontalLeftCode (path.take j) start
      htakeValid
    have hinitial : ((level - 1 : Nat) : Int) = start.1 := by
      push_cast
      omega
    have hline' : lineFreeEndpoint start.1
        ((horizontalLeftCode path).take j) =
          (isingDiagonalWalkEndpoint start (path.take j)).1 := by
      simpa only [horizontalLeftCode, List.map_take] using hline
    rw [← hinitial] at hline'
    have hendpoint :
        (isingDiagonalWalkEndpoint start (path.take j)).1 = level := by
      exact_mod_cast hline'.symm.trans hright
    have hfirst := reflectPrefix_firstHit split w.1.1.2.1 j (by simpa)
    apply hfirst
    have hstartEq : reflectedEndpoint (level : Int)
        (reflectedEndpoint (level : Int) start) = start :=
      reflectedEndpoint_reflectedEndpoint (level : Int) start
    have hendpoint' :
        (isingDiagonalWalkEndpoint
          (reflectedEndpoint (level : Int)
            (reflectedEndpoint (level : Int) start)) (path.take j)).1 =
          level := by simpa using hendpoint
    dsimp [path] at hendpoint'
    unfold steps at hendpoint'
    have hjref : j ≤ split.reflectPrefix.before.length := by
      simpa [reflectPrefix] using hjbefore.le
    rw [List.take_append_of_le_length hjref] at hendpoint'
    exact hendpoint'
  have hstartNonneg : 0 ≤ ((level - 1 : Nat) : Int) := by omega
  have hstartLt : ((level - 1 : Nat) : Int) < (level : Nat) := by
    push_cast
    omega
  have hrun := intLineChoiceRun_eq_zero_of_free_hit level
    ((level - 1 : Nat) : Int) (horizontalLeftCode path) k
    hstartNonneg hstartLt (by simpa [horizontalLeftCode] using hkpath)
    hfreeHit hnoRight
  have hagree := intLineChoiceRun_eq_lineChoiceRun_val level
    (leftGapNeighbor level hlevel) (horizontalLeftCode path)
  apply Fin.ext
  have hvalInt : ((isingLineChoiceRun level
      (leftGapNeighbor level hlevel) (horizontalLeftCode path)).1 : Int) =
      0 := by
    rw [← hagree]
    simpa [leftGapNeighbor] using hrun
  change (isingLineChoiceRun level (leftGapNeighbor level hlevel)
    (horizontalLeftCode path)).1 = 0
  exact_mod_cast hvalInt

theorem horizontalLeftCode_verticalCode_injective_of_valid
    {a b : List (Int × Int)}
    (ha : IsingDiagonalWalkStepsValid a)
    (hb : IsingDiagonalWalkStepsValid b)
    (hh : horizontalLeftCode a = horizontalLeftCode b)
    (hv : verticalCode a = verticalCode b) : a = b := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => rfl
      | cons e b => simp [horizontalLeftCode] at hh
  | cons d a ih =>
      cases b with
      | nil => simp [horizontalLeftCode] at hh
      | cons e b =>
          simp only [horizontalLeftCode, verticalCode, List.map_cons,
            List.cons.injEq] at hh hv
          have hd := ha d (by simp)
          have he := hb e (by simp)
          have hde : d = e := by
            rcases hd with ⟨hdx | hdx, hdy | hdy⟩ <;>
              rcases he with ⟨hex | hex, hey | hey⟩ <;>
              simp [hdx, hdy, hex, hey] at hh hv
            all_goals apply Prod.ext <;> simp_all
          subst e
          congr 1
          apply ih
          · intro z hz
            exact ha z (by simp [hz])
          · intro z hz
            exact hb z (by simp [hz])
          · exact hh.2
          · exact hv.2

end IsingDiagonalWalkHitSplit
end StatMech.Universality

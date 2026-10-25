/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part5


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

theorem survivalExceptional_horizontal_run_left
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R)
    (w : SurvivalExceptionalFirstHitFamily R start (level : Int)
      walkLength target) :
    isingLineChoiceRun (R - level) (rightGapNeighbor R level hgap)
        (horizontalRightCode w.1.1.1.reflectPrefix.steps) =
      rightGapLeft R level := by
  let split := w.1.1.1
  let path := split.reflectPrefix.steps
  let n := R - level
  have hrefValid : IsingDiagonalWalkStepsValid path :=
    reflectPrefix_valid split w.1.1.2.2.1
  rcases survivalExceptional_reflected_exists_hit_right R start (level : Int)
      walkLength target hstart (by exact_mod_cast hlevel)
      (by exact_mod_cast hgap) w with ⟨k, hkbefore, hhit⟩
  change k < split.before.length at hkbefore
  change (isingDiagonalWalkEndpoint (reflectedEndpoint (level : Int) start)
    (path.take k)).1 = R at hhit
  have hkpath : k ≤ path.length := by
    dsimp [path]
    rw [reflectPrefix_length]
    unfold steps
    simp only [List.length_append]
    exact le_trans hkbefore.le (Nat.le_add_right _ _)
  have hfreeHit :
      lineFreeEndpoint ((R - level - 1 : Nat) : Int)
          ((horizontalRightCode path).take k) = 0 := by
    have htakeValid : IsingDiagonalWalkStepsValid (path.take k) := by
      intro d hd
      exact hrefValid d (List.mem_of_mem_take hd)
    have hline := lineFreeEndpoint_horizontalRightCode
      (path.take k) (reflectedEndpoint (level : Int) start) (R : Int)
      htakeValid
    have hinitial :
        ((R - level - 1 : Nat) : Int) =
          (R : Int) - (reflectedEndpoint (level : Int) start).1 := by
      unfold reflectedEndpoint
      dsimp
      push_cast
      omega
    have hline' : lineFreeEndpoint ((R : Int) -
        (reflectedEndpoint (level : Int) start).1)
        ((horizontalRightCode path).take k) =
          (R : Int) - (isingDiagonalWalkEndpoint
            (reflectedEndpoint (level : Int) start) (path.take k)).1 := by
      simpa only [horizontalRightCode, List.map_take] using hline
    rw [← hinitial, hhit] at hline'
    simpa using hline'
  have hnoRight : ∀ j, j < k →
      lineFreeEndpoint ((R - level - 1 : Nat) : Int)
        ((horizontalRightCode path).take j) ≠ (R - level : Nat) := by
    intro j hj hright
    have hjbefore : j < split.before.length := by omega
    have htakeValid : IsingDiagonalWalkStepsValid (path.take j) := by
      intro d hd
      exact hrefValid d (List.mem_of_mem_take hd)
    have hline := lineFreeEndpoint_horizontalRightCode
      (path.take j) (reflectedEndpoint (level : Int) start) (R : Int)
      htakeValid
    have hinitial :
        ((R - level - 1 : Nat) : Int) =
          (R : Int) - (reflectedEndpoint (level : Int) start).1 := by
      unfold reflectedEndpoint
      dsimp
      push_cast
      omega
    have hline' : lineFreeEndpoint ((R : Int) -
        (reflectedEndpoint (level : Int) start).1)
        ((horizontalRightCode path).take j) =
          (R : Int) - (isingDiagonalWalkEndpoint
            (reflectedEndpoint (level : Int) start) (path.take j)).1 := by
      simpa only [horizontalRightCode, List.map_take] using hline
    rw [← hinitial] at hline'
    have hendpoint :
        (isingDiagonalWalkEndpoint (reflectedEndpoint (level : Int) start)
          (path.take j)).1 = level := by
      push_cast at hright
      omega
    have hfirst := reflectPrefix_firstHit split w.1.1.2.1 j (by simpa)
    apply hfirst
    dsimp [path] at hendpoint
    unfold steps at hendpoint
    have hjref : j ≤ split.reflectPrefix.before.length := by
      simpa [reflectPrefix] using hjbefore.le
    rw [List.take_append_of_le_length hjref] at hendpoint
    exact hendpoint
  have hstartNonneg : 0 ≤ ((R - level - 1 : Nat) : Int) := by omega
  have hstartLt : ((R - level - 1 : Nat) : Int) < (R - level : Nat) := by
    push_cast
    omega
  have hrun := intLineChoiceRun_eq_zero_of_free_hit (R - level)
    ((R - level - 1 : Nat) : Int) (horizontalRightCode path) k
    hstartNonneg hstartLt (by simpa [horizontalRightCode] using hkpath)
    hfreeHit hnoRight
  have hagree := intLineChoiceRun_eq_lineChoiceRun_val (R - level)
    (rightGapNeighbor R level hgap) (horizontalRightCode path)
  apply Fin.ext
  have hvalInt : ((isingLineChoiceRun (R - level)
      (rightGapNeighbor R level hgap) (horizontalRightCode path)).1 : Int) =
      0 := by
    rw [← hagree]
    simpa [rightGapNeighbor] using hrun
  change (isingLineChoiceRun (R - level) (rightGapNeighbor R level hgap)
    (horizontalRightCode path)).1 = 0
  exact_mod_cast hvalInt

theorem horizontalRightCode_verticalCode_injective_of_valid
    {a b : List (Int × Int)}
    (ha : IsingDiagonalWalkStepsValid a)
    (hb : IsingDiagonalWalkStepsValid b)
    (hh : horizontalRightCode a = horizontalRightCode b)
    (hv : verticalCode a = verticalCode b) : a = b := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => rfl
      | cons e b => simp [horizontalRightCode] at hh
  | cons d a ih =>
      cases b with
      | nil => simp [horizontalRightCode] at hh
      | cons e b =>
          simp only [horizontalRightCode, verticalCode, List.map_cons,
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

theorem reflectPrefix_verticalCode_endpoint
    {start : Int × Int} {level : Int} {walkLength : Nat}
    {target : Int × Int}
    (w : FirstHitFamily start level walkLength target) :
    lineFreeEndpoint start.2 (verticalCode w.1.reflectPrefix.steps) =
      target.2 := by
  have hvalid := reflectPrefix_valid w.1 w.2.2.1
  have hline := lineFreeEndpoint_verticalCode w.1.reflectPrefix.steps
    (reflectedEndpoint level start) hvalid
  calc
    lineFreeEndpoint start.2 (verticalCode w.1.reflectPrefix.steps) =
        (isingDiagonalWalkEndpoint (reflectedEndpoint level start)
          w.1.reflectPrefix.steps).2 := hline
    _ = w.1.reflectPrefix.endpoint.2 := rfl
    _ = w.1.endpoint.2 := congrArg Prod.snd (reflectPrefix_endpoint w.1)
    _ = target.2 := congrArg Prod.snd w.2.2.2.2

end IsingDiagonalWalkHitSplit
end StatMech.Universality

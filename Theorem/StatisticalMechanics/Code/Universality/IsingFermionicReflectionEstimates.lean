/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

theorem lineFreeEndpoint_horizontalRightCode
    (path : List (Int × Int)) (start : Int × Int) (right : Int)
    (hvalid : IsingDiagonalWalkStepsValid path) :
    lineFreeEndpoint (right - start.1) (horizontalRightCode path) =
      right - (isingDiagonalWalkEndpoint start path).1 := by
  induction path generalizing start with
  | nil => simp [lineFreeEndpoint, horizontalRightCode,
      isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
  | cons d path ih =>
      have hd := hvalid d (by simp)
      have htail : IsingDiagonalWalkStepsValid path := by
        intro e he
        exact hvalid e (by simp [he])
      have hih := ih (isingDiagonalWalkNext start d) htail
      have hstep :
          right - start.1 + (if decide (d.1 = -1) then 1 else -1) =
            right - (isingDiagonalWalkNext start d).1 := by
        rcases hd.1 with hd | hd <;>
          simp [hd, isingDiagonalWalkNext] <;> omega
      rw [horizontalRightCode, List.map_cons, lineFreeEndpoint, hstep]
      simpa [isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement,
        isingDiagonalWalkNext, add_assoc] using hih

theorem lineFreeEndpoint_horizontalLeftCode
    (path : List (Int × Int)) (start : Int × Int)
    (hvalid : IsingDiagonalWalkStepsValid path) :
    lineFreeEndpoint start.1 (horizontalLeftCode path) =
      (isingDiagonalWalkEndpoint start path).1 := by
  induction path generalizing start with
  | nil => simp [lineFreeEndpoint, horizontalLeftCode,
      isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
  | cons d path ih =>
      have hd := hvalid d (by simp)
      have htail : IsingDiagonalWalkStepsValid path := by
        intro e he
        exact hvalid e (by simp [he])
      have hih := ih (isingDiagonalWalkNext start d) htail
      have hstep :
          start.1 + (if decide (d.1 = 1) then 1 else -1) =
            (isingDiagonalWalkNext start d).1 := by
        rcases hd.1 with hd | hd <;>
          simp [hd, isingDiagonalWalkNext] <;> omega
      rw [horizontalLeftCode, List.map_cons, lineFreeEndpoint, hstep]
      simpa [isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement,
        isingDiagonalWalkNext, add_assoc] using hih

theorem lineFreeEndpoint_verticalCode
    (path : List (Int × Int)) (start : Int × Int)
    (hvalid : IsingDiagonalWalkStepsValid path) :
    lineFreeEndpoint start.2 (verticalCode path) =
      (isingDiagonalWalkEndpoint start path).2 := by
  induction path generalizing start with
  | nil => simp [lineFreeEndpoint, verticalCode,
      isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
  | cons d path ih =>
      have hd := hvalid d (by simp)
      have htail : IsingDiagonalWalkStepsValid path := by
        intro e he
        exact hvalid e (by simp [he])
      have hih := ih (isingDiagonalWalkNext start d) htail
      have hstep :
          start.2 + (if decide (d.2 = 1) then 1 else -1) =
            (isingDiagonalWalkNext start d).2 := by
        rcases hd.2 with hd | hd <;>
          simp [hd, isingDiagonalWalkNext] <;> omega
      rw [verticalCode, List.map_cons, lineFreeEndpoint, hstep]
      simpa [isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement,
        isingDiagonalWalkNext, add_assoc] using hih

end IsingDiagonalWalkHitSplit
end StatMech.Universality

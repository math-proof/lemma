/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDualShift.Part3
import Def.StatisticalMechanics.Code.FK.TriHexPeriodicVertexGeometry.Part4
open Set


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem triangularStraightEdgeArc_injective {x y : Site 2}
    (hxy : triangularGraph.Adj x y) :
    Function.Injective (triangularStraightEdgeArc hxy) := by
  apply Path.segment_injective_of_ne
  exact triangularPlaneVertex.injective.ne hxy.ne

theorem triangularStraightEdgeArc_symm {x y : Site 2}
    (hxy : triangularGraph.Adj x y) :
    Set.range (triangularStraightEdgeArc hxy.symm) =
      Set.range (triangularStraightEdgeArc hxy) := by
  simp only [triangularStraightEdgeArc, Path.range_segment]
  exact segment_symm Real _ _

theorem triangularStraightEdgeArc_shift
    (z : Site 2) {x y : Site 2} (hxy : triangularGraph.Adj x y) :
    Set.range (triangularStraightEdgeArc
        ((triangular.shift_adj z x y).2 hxy)) =
      (fun p => p + triHexPlanePeriod z) ''
        Set.range (triangularStraightEdgeArc hxy) := by
  simp only [triangularStraightEdgeArc, Path.range_segment,
    triangularPlaneVertex_shift]
  simpa [add_comm] using
    (segment_translate_image Real (triHexPlanePeriod z)
      (triangularPlaneVertex x) (triangularPlaneVertex y)).symm

theorem triangularStraightEdge_length_le_two {x y : Site 2}
    (hxy : triangularGraph.Adj x y) :
    dist (triangularPlaneVertex x) (triangularPlaneVertex y) <= 2 := by
  rw [triangularGraph_adj, triangularAdj] at hxy
  obtain ⟨i, h | h⟩ := hxy
  · have hy : y = x + triangularStep i := by
      ext j
      have hj := congrFun h j
      simp only [Pi.sub_apply, Pi.add_apply] at hj ⊢
      omega
    subst y
    change dist (triHexPlanePeriod x)
      (triHexPlanePeriod (x + triangularStep i)) <= 2
    calc
      dist (triHexPlanePeriod x)
          (triHexPlanePeriod (x + triangularStep i)) =
          ‖triHexPlanePeriod (triangularStep i)‖ := by
        rw [map_add, dist_eq_norm]
        have heq : triHexPlanePeriod x -
            (triHexPlanePeriod x + triHexPlanePeriod (triangularStep i)) =
              -triHexPlanePeriod (triangularStep i) := by abel
        rw [heq, norm_neg]
      _ <= 2 := by
        calc
          ‖triHexPlanePeriod (triangularStep i)‖ <=
              |(triHexPlanePeriod (triangularStep i)).re| +
                |(triHexPlanePeriod (triangularStep i)).im| :=
            Complex.norm_le_abs_re_add_abs_im _
          _ <= 2 := by
            fin_cases i <;> norm_num [triHexPlanePeriod, triangularStep]
  · have hx : x = y + triangularStep i := by
      ext j
      have hj := congrFun h j
      simp only [Pi.sub_apply, Pi.add_apply] at hj ⊢
      omega
    subst x
    change dist (triHexPlanePeriod (y + triangularStep i))
      (triHexPlanePeriod y) <= 2
    calc
      dist (triHexPlanePeriod (y + triangularStep i))
          (triHexPlanePeriod y) =
          ‖triHexPlanePeriod (triangularStep i)‖ := by
        rw [map_add, dist_eq_norm]
        congr 1
        abel
      _ <= 2 := by
        calc
          ‖triHexPlanePeriod (triangularStep i)‖ <=
              |(triHexPlanePeriod (triangularStep i)).re| +
                |(triHexPlanePeriod (triangularStep i)).im| :=
            Complex.norm_le_abs_re_add_abs_im _
          _ <= 2 := by
            fin_cases i <;> norm_num [triHexPlanePeriod, triangularStep]


end StatMech.FK.PeriodicPlanar

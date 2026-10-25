/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDualShift.Part3
import Def.StatisticalMechanics.Code.FK.TriHexPeriodicVertexGeometry.Part8
open Set


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem hexagonalStraightEdgeArc_injective {u v : HexVertex}
    (huv : hexagonalGraph.Adj u v) :
    Function.Injective (hexagonalStraightEdgeArc huv) := by
  apply Path.segment_injective_of_ne
  exact hexagonalPlaneVertex.injective.ne huv.ne

theorem hexagonalStraightEdgeArc_symm {u v : HexVertex}
    (huv : hexagonalGraph.Adj u v) :
    Set.range (hexagonalStraightEdgeArc huv.symm) =
      Set.range (hexagonalStraightEdgeArc huv) := by
  simp only [hexagonalStraightEdgeArc, Path.range_segment]
  exact segment_symm Real _ _

theorem hexagonalStraightEdgeArc_shift
    (z : Site 2) {u v : HexVertex} (huv : hexagonalGraph.Adj u v) :
    Set.range (hexagonalStraightEdgeArc
        ((hexagonal.shift_adj z u v).2 huv)) =
      (fun p => p + triHexPlanePeriod z) ''
        Set.range (hexagonalStraightEdgeArc huv) := by
  simp only [hexagonalStraightEdgeArc, Path.range_segment,
    hexagonalPlaneVertex_shift]
  simpa [add_comm] using
    (segment_translate_image Real (triHexPlanePeriod z)
      (hexagonalPlaneVertex u) (hexagonalPlaneVertex v)).symm

theorem hexagonalStraightEdge_length_le_two {u v : HexVertex}
    (huv : hexagonalGraph.Adj u v) :
    dist (hexagonalPlaneVertex u) (hexagonalPlaneVertex v) <= 2 := by
  rw [hexagonalGraph_adj, hexagonalAdj] at huv
  rcases huv with ⟨hu, hv, i, h⟩ | ⟨hv, hu, i, h⟩
  · rcases u with ⟨x, xb⟩
    rcases v with ⟨y, yb⟩
    change xb = false at hu
    change yb = true at hv
    subst xb
    subst yb
    have hy : y = x + hexagonalStep i := by
      ext j
      have hj := congrFun h j
      simp only [Pi.sub_apply, Pi.add_apply] at hj ⊢
      omega
    subst y
    change dist
      (triHexPlanePeriod x + hexagonalFaceCenterOffset false)
      (triHexPlanePeriod (x + hexagonalStep i) +
        hexagonalFaceCenterOffset true) <= 2
    calc
      _ = ‖hexagonalFaceCenterOffset false -
          (triHexPlanePeriod (hexagonalStep i) +
            hexagonalFaceCenterOffset true)‖ := by
        rw [map_add, dist_eq_norm]
        congr 1
        abel
      _ <= 2 := by
        let d := hexagonalFaceCenterOffset false -
          (triHexPlanePeriod (hexagonalStep i) +
            hexagonalFaceCenterOffset true)
        calc
          ‖hexagonalFaceCenterOffset false -
              (triHexPlanePeriod (hexagonalStep i) +
                hexagonalFaceCenterOffset true)‖ <= |d.re| + |d.im| :=
            Complex.norm_le_abs_re_add_abs_im d
          _ <= 2 := by
            fin_cases i <;>
              norm_num [d, hexagonalFaceCenterOffset, triHexPlanePeriod,
                hexagonalStep]
  · rcases u with ⟨x, xb⟩
    rcases v with ⟨y, yb⟩
    change yb = false at hv
    change xb = true at hu
    subst xb
    subst yb
    have hx : x = y + hexagonalStep i := by
      ext j
      have hj := congrFun h j
      simp only [Pi.sub_apply, Pi.add_apply] at hj ⊢
      omega
    subst x
    change dist
      (triHexPlanePeriod (y + hexagonalStep i) +
        hexagonalFaceCenterOffset true)
      (triHexPlanePeriod y + hexagonalFaceCenterOffset false) <= 2
    calc
      _ = ‖triHexPlanePeriod (hexagonalStep i) +
          hexagonalFaceCenterOffset true -
            hexagonalFaceCenterOffset false‖ := by
        rw [map_add, dist_eq_norm]
        congr 1
        abel
      _ <= 2 := by
        let d := triHexPlanePeriod (hexagonalStep i) +
          hexagonalFaceCenterOffset true -
            hexagonalFaceCenterOffset false
        calc
          ‖triHexPlanePeriod (hexagonalStep i) +
              hexagonalFaceCenterOffset true -
                hexagonalFaceCenterOffset false‖ <= |d.re| + |d.im| :=
            Complex.norm_le_abs_re_add_abs_im d
          _ <= 2 := by
            fin_cases i <;>
              norm_num [d, hexagonalFaceCenterOffset, triHexPlanePeriod,
                hexagonalStep]

theorem segment_endpoints_norm_le_add_two
    (a b : Complex) (t : unitInterval) (R : Real)
    (hpoint : ‖Path.segment a b t‖ <= R)
    (hlength : dist a b <= 2) :
    ‖a‖ <= R + 2 ∧ ‖b‖ <= R + 2 := by
  have ht : ‖(t : Real)‖ <= 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg t.2.1]
    exact t.2.2
  have hOneSub : ‖(1 : Real) - t‖ <= 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr t.2.2)]
    linarith [t.2.1]
  have hleft : dist a (Path.segment a b t) <= 2 := by
    rw [Path.segment_apply, dist_left_lineMap]
    calc
      ‖(t : Real)‖ * dist a b <= 1 * 2 :=
        mul_le_mul ht hlength (dist_nonneg) (by norm_num)
      _ = 2 := by norm_num
  have hright : dist b (Path.segment a b t) <= 2 := by
    rw [Path.segment_apply, dist_right_lineMap]
    calc
      ‖(1 : Real) - t‖ * dist a b <= 1 * 2 :=
        mul_le_mul hOneSub hlength (dist_nonneg) (by norm_num)
      _ = 2 := by norm_num
  constructor
  · calc
      ‖a‖ = dist a 0 := by rw [dist_zero_right]
      _ <= dist a (Path.segment a b t) +
          dist (Path.segment a b t) 0 := dist_triangle _ _ _
      _ <= 2 + R := by
        rw [dist_zero_right]
        exact add_le_add hleft hpoint
      _ = R + 2 := by ring
  · calc
      ‖b‖ = dist b 0 := by rw [dist_zero_right]
      _ <= dist b (Path.segment a b t) +
          dist (Path.segment a b t) 0 := dist_triangle _ _ _
      _ <= 2 + R := by
        rw [dist_zero_right]
        exact add_le_add hright hpoint
      _ = R + 2 := by ring


theorem triangularStraightEdgeArc_locallyFinite
    (K : Set Complex) (hK : IsCompact K) :
    {xy : Site 2 × Site 2 | ∃ hxy : triangularGraph.Adj xy.1 xy.2,
      (Set.range (triangularStraightEdgeArc hxy) ∩ K).Nonempty}.Finite := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Complex)
  let B : Set (Site 2) :=
    {x | ‖(triangularPlaneVertex x : Complex)‖ <= R + 2}
  have hB : B.Finite := triangularPlaneVertex_bounded_finite (R + 2)
  apply (hB.prod hB).subset
  rintro ⟨x, y⟩ ⟨hxy, q, hqArc, hqK⟩
  obtain ⟨t, rfl⟩ := hqArc
  have hpoint :
      ‖triangularStraightEdgeArc hxy t‖ <= R := by
    have hmem := hR hqK
    simpa [Metric.mem_closedBall, dist_zero_right] using hmem
  have hend := segment_endpoints_norm_le_add_two
    (triangularPlaneVertex x) (triangularPlaneVertex y) t R
    (by simpa [triangularStraightEdgeArc] using hpoint)
    (triangularStraightEdge_length_le_two hxy)
  exact hend


theorem hexagonalStraightEdgeArc_locallyFinite
    (K : Set Complex) (hK : IsCompact K) :
    {uv : HexVertex × HexVertex | ∃ huv : hexagonalGraph.Adj uv.1 uv.2,
      (Set.range (hexagonalStraightEdgeArc huv) ∩ K).Nonempty}.Finite := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Complex)
  let B : Set HexVertex :=
    {u | ‖(hexagonalPlaneVertex u : Complex)‖ <= R + 2}
  have hB : B.Finite := hexagonalPlaneVertex_bounded_finite (R + 2)
  apply (hB.prod hB).subset
  rintro ⟨u, v⟩ ⟨huv, q, hqArc, hqK⟩
  obtain ⟨t, rfl⟩ := hqArc
  have hpoint :
      ‖hexagonalStraightEdgeArc huv t‖ <= R := by
    have hmem := hR hqK
    simpa [Metric.mem_closedBall, dist_zero_right] using hmem
  have hend := segment_endpoints_norm_le_add_two
    (hexagonalPlaneVertex u) (hexagonalPlaneVertex v) t R
    (by simpa [hexagonalStraightEdgeArc] using hpoint)
    (hexagonalStraightEdge_length_le_two huv)
  exact hend

end StatMech.FK.PeriodicPlanar

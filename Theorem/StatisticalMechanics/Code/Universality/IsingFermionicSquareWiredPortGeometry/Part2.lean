/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareWiredIntPoint_injective :
    Function.Injective fkIsingSquareWiredIntPoint := by
  rintro ⟨px, py⟩ ⟨qx, qy⟩ h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [fkIsingSquareWiredIntPoint] at hre him
  apply Prod.ext
  · exact_mod_cast hre
  · exact_mod_cast him


theorem fkIsingSquareWiredIntPoint_not_strictly_between_unitDiagonal
    (p q : Int × Int) (a : Fin 4) :
    ¬Sbtw Real (fkIsingSquareWiredIntPoint p)
      (fkIsingSquareWiredIntPoint q)
      (fkIsingSquareWiredIntPoint
        (p + fkIsingSquareWiredUnitDiagonalStep a)) := by
  intro hbetween
  obtain ⟨t, ⟨ht0, ht1⟩, ht⟩ := hbetween.mem_image_Ioo
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  have hre := congrArg Complex.re ht
  fin_cases a <;>
    simp [fkIsingSquareWiredIntPoint,
      fkIsingSquareWiredUnitDiagonalStep,
      AffineMap.lineMap_apply] at hre
  · have hloR : (-1 : Real) < (qx : Real) - px := by linarith
    have hhiR : (qx : Real) - px < 0 := by linarith
    have hlo : (-1 : Int) < qx - px := by exact_mod_cast hloR
    have hhi : qx - px < 0 := by exact_mod_cast hhiR
    omega
  · have hloR : (-1 : Real) < (qx : Real) - px := by linarith
    have hhiR : (qx : Real) - px < 0 := by linarith
    have hlo : (-1 : Int) < qx - px := by exact_mod_cast hloR
    have hhi : qx - px < 0 := by exact_mod_cast hhiR
    omega
  · have hloR : (0 : Real) < (qx : Real) - px := by linarith
    have hhiR : (qx : Real) - px < 1 := by linarith
    have hlo : (0 : Int) < qx - px := by exact_mod_cast hloR
    have hhi : qx - px < 1 := by exact_mod_cast hhiR
    omega
  · have hloR : (0 : Real) < (qx : Real) - px := by linarith
    have hhiR : (qx : Real) - px < 1 := by linarith
    have hlo : (0 : Int) < qx - px := by exact_mod_cast hloR
    have hhi : qx - px < 1 := by exact_mod_cast hhiR
    omega


theorem fkIsingSquareWiredUnitDiagonal_open_intersection_midpoint_eq
    (p q : Int × Int) (a b : Fin 4) (z : Complex)
    (hp : Sbtw Real (fkIsingSquareWiredIntPoint p) z
      (fkIsingSquareWiredIntPoint
        (p + fkIsingSquareWiredUnitDiagonalStep a)))
    (hq : Sbtw Real (fkIsingSquareWiredIntPoint q) z
      (fkIsingSquareWiredIntPoint
        (q + fkIsingSquareWiredUnitDiagonalStep b))) :
    p + (p + fkIsingSquareWiredUnitDiagonalStep a) =
      q + (q + fkIsingSquareWiredUnitDiagonalStep b) := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  obtain ⟨t, ⟨ht0, ht1⟩, htz⟩ := hp.mem_image_Ioo
  obtain ⟨u, ⟨hu0, hu1⟩, huz⟩ := hq.mem_image_Ioo
  have heq : AffineMap.lineMap (fkIsingSquareWiredIntPoint (px, py))
        (fkIsingSquareWiredIntPoint
          ((px, py) + fkIsingSquareWiredUnitDiagonalStep a)) t =
      AffineMap.lineMap (fkIsingSquareWiredIntPoint (qx, qy))
        (fkIsingSquareWiredIntPoint
          ((qx, qy) + fkIsingSquareWiredUnitDiagonalStep b)) u :=
    htz.trans huz.symm
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  fin_cases a <;> fin_cases b <;>
    simp [fkIsingSquareWiredIntPoint,
      fkIsingSquareWiredUnitDiagonalStep,
      AffineMap.lineMap_apply, Prod.ext_iff] at hre him ⊢
  all_goals
    have hxloR : (-2 : Real) < (qx : Real) - (px : Real) := by linarith
    have hxhiR : (qx : Real) - (px : Real) < 2 := by linarith
    have hyloR : (-2 : Real) < (qy : Real) - (py : Real) := by linarith
    have hyhiR : (qy : Real) - (py : Real) < 2 := by linarith
    have hxlo : (-2 : Int) < qx - px := by exact_mod_cast hxloR
    have hxhi : qx - px < (2 : Int) := by exact_mod_cast hxhiR
    have hylo : (-2 : Int) < qy - py := by exact_mod_cast hyloR
    have hyhi : qy - py < (2 : Int) := by exact_mod_cast hyhiR
    interval_cases hx : qx - px <;>
      interval_cases hy : qy - py <;>
      have hxR := congrArg (fun x : Int => (x : Real)) hx <;>
      have hyR := congrArg (fun x : Int => (x : Real)) hy <;>
      push_cast at hxR hyR <;>
      first
      | constructor <;> omega
      | (exfalso; linarith)


end
end StatMech.Universality

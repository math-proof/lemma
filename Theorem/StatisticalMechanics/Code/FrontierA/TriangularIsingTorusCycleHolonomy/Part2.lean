/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSurfaceTwist
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open scoped Affine


theorem triangularIntPoint_injective :
    Function.Injective triangularIntPoint := by
  rintro ⟨px, py⟩ ⟨qx, qy⟩ h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [triangularIntPoint] at hre him
  apply Prod.ext
  · exact_mod_cast hre
  · exact_mod_cast him


theorem triangularIntPoint_not_strictly_between_step
    (p q : Int × Int) (a : Fin 6)
    (hqp : q ≠ p) (hqend : q ≠ p + triangularIntStep a) :
    ¬Sbtw Real (triangularIntPoint p) (triangularIntPoint q)
      (triangularIntPoint (p + triangularIntStep a)) := by
  intro hbetween
  obtain ⟨t, ⟨ht0, ht1⟩, ht⟩ := hbetween.mem_image_Ioo
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  have hre := congrArg Complex.re ht
  have him := congrArg Complex.im ht
  fin_cases a <;>
    simp [triangularIntPoint, triangularIntStep,
      AffineMap.lineMap_apply, Prod.ext_iff] at hre him hqp hqend
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
  · have hloR : (-1 : Real) < (qy : Real) - py := by linarith
    have hhiR : (qy : Real) - py < 0 := by linarith
    have hlo : (-1 : Int) < qy - py := by exact_mod_cast hloR
    have hhi : qy - py < 0 := by exact_mod_cast hhiR
    omega
  · have hloR : (0 : Real) < (qy : Real) - py := by linarith
    have hhiR : (qy : Real) - py < 1 := by linarith
    have hlo : (0 : Int) < qy - py := by exact_mod_cast hloR
    have hhi : qy - py < 1 := by exact_mod_cast hhiR
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

end StatMech.FrontierA

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearFormal.Part5
import Def.StatisticalMechanics.Code.FrontierA.KacWardAngleGauge.Part3
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager


theorem kwPrincipalHalfAngleRoot_ne_zero
    {D : Type*} (angle : D → Real.Angle) (dart : D) :
    kwPrincipalHalfAngleRoot angle dart ≠ 0 :=
  kwRealHalfAngleRoot_ne_zero _ _

theorem kwPrincipalHalfAngleRoot_sq
    {D : Type*} (angle : D → Real.Angle) (dart : D) :
    kwPrincipalHalfAngleRoot angle dart ^ 2 =
      Complex.exp (((angle dart).toReal : ℂ) * Complex.I) := by
  unfold kwPrincipalHalfAngleRoot kwRealHalfAngleRoot
  rw [pow_two, ← Complex.exp_add]
  congr 1
  ring

theorem kwPrincipalHalfAnglePhase_sq
    {D : Type*} (angle : D → Real.Angle) (dart next : D) :
    kwPrincipalHalfAnglePhase angle dart next ^ 2 =
      Complex.exp
        (((angle next - angle dart).toReal : ℂ) * Complex.I) := by
  unfold kwPrincipalHalfAnglePhase
  rw [pow_two, ← Complex.exp_add]
  congr 1
  ring


end StatMech.FrontierA

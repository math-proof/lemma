/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearFormal.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngleGauge.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager


noncomputable def kwPrincipalHalfAnglePhase
    {D : Type*} (angle : D → Real.Angle) : D → D → ℂ :=
  fun dart next ↦ Complex.exp
    (((angle next - angle dart).toReal : ℂ) * Complex.I / 2)


noncomputable def kwPrincipalHalfAngleRoot
    {D : Type*} (angle : D → Real.Angle) : D → ℂ :=
  kwRealHalfAngleRoot (fun dart ↦ (angle dart).toReal)

end StatMech.FrontierA

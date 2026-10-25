/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearFormal.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngleGauge
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager


noncomputable def kwBranchHalfAnglePhase
    {D : Type*} (root : D → ℂ) (branch : D → D → ℂ) : D → D → ℂ :=
  fun dart next ↦ (root dart)⁻¹ * branch dart next * root next


noncomputable def kwRealHalfAngleRoot
    {D : Type*} (angle : D → ℝ) : D → ℂ :=
  fun dart ↦ Complex.exp (((angle dart : ℂ) * Complex.I) / 2)

end StatMech.FrontierA

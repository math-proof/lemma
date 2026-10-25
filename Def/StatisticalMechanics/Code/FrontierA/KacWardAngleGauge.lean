/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngleGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearFormal.Part5
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager


noncomputable def kwPhaseGauge
    {D : Type*} (gauge : D → ℂ) (phase : D → D → ℂ) : D → D → ℂ :=
  fun dart next ↦ (gauge dart)⁻¹ * phase dart next * gauge next


end StatMech.FrontierA

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SWModuliGoal62.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part8
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.FourManifoldsSW
import Class.v1.Atlas.GeometryOfManifolds.code.SWModuliGoal62
set_option autoImplicit false


/-- Two SW solutions are gauge-equivalent if some element $f \in \mathcal{G}$ of the gauge group maps one to the other. -/
def SWGaugeEquivalent
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gauge : GaugeActionData spinc)
    (sol₁ sol₂ : SWSolution spinc) : Prop :=
  ∃ (f : gauge.GaugeGroup), gauge.gauge_action f sol₁ = sol₂


/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SWModuliQuotient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.GaugeAction.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.GaugeAction
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SWModuliGoal62
import Structure.v1.Atlas.GeometryOfManifolds.code.SWModuliGoal62
set_option autoImplicit false


noncomputable section

/-- Gauge-invariant sup-norm-squared $\|\Phi\|_\infty^2$ descends to the moduli quotient. -/
def SWModuliQuotient.supNormSq
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gd : GaugeActionData spinc)
    (q : SWModuliQuotient gd) : ℝ :=
  Quotient.lift (fun sol => sol.supNormSq)
    (by
      intro a b hab
      obtain ⟨g, hg⟩ := hab
      rw [← hg]
      exact (gd.gauge_action_preserves_supNormSq g a).symm) q


/-- A moduli class is reducible iff its sup-norm-squared vanishes, i.e. the spinor field $\Phi$
is identically zero. -/
def SWModuliQuotient.IsReducible
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gd : GaugeActionData spinc)
    (q : SWModuliQuotient gd) : Prop :=
  SWModuliQuotient.supNormSq gd q = 0

end

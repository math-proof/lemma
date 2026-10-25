/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.ContinuousFunctions.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.ContinuousFunctions
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Theorem.v1.Atlas.DifferentialAnalysis.code.JordanDecomposition.Part4


namespace ContinuousFunctions

open ContinuousLinearMap

section PosPartConstruction

variable {X : Type*} [MetricSpace X]

/-- The positive part of a continuous linear functional `u` packaged as a linear map. -/
noncomputable def posPartLinearMap (u : C₀Map X →L[ℝ] ℝ) : C₀Map X →ₗ[ℝ] ℝ where
  toFun := posPartFn u
  map_add' := posPartFn_add u
  map_smul' c f := by
    simp only [posPartFn_smul, smul_eq_mul, RingHom.id_apply]

/-- The positive part of a continuous linear functional `u` on `C₀(X, ℝ)`, packaged as a CLM. -/
noncomputable def posPartCLM {X : Type*} [MetricSpace X]
    (u : C₀Map X →L[ℝ] ℝ) : C₀Map X →L[ℝ] ℝ :=
  (posPartLinearMap u).mkContinuous ‖u‖ (fun f => posPartFn_bound u f)

end PosPartConstruction
end ContinuousFunctions

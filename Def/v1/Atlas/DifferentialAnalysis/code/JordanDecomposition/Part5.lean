module
public import Def.v1.Atlas.DifferentialAnalysis.code.ContinuousFunctions.Part2
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.ContinuousFunctions
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Theorem.v1.Atlas.DifferentialAnalysis.code.JordanDecomposition.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part5
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierDensity
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourierRootDensity (lam alpha : Real) : Real :=
  1 / 2 + ∑' n : Nat, sixVertexFourierRootDensityTerm lam n alpha

end
end StatMech.FrontierD

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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierDensity.Part2
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourierRootDensityTermContinuous
    (lam : Real) (n : Nat) : C(Real, Real) :=
  ⟨sixVertexFourierRootDensityTerm lam n, by
    unfold sixVertexFourierRootDensityTerm
    fun_prop⟩

end
end StatMech.FrontierD

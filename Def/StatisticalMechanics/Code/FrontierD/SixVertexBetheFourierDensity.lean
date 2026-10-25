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
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourierRootDensityTerm (lam : Real) (n : Nat) (alpha : Real) : Real :=
  Real.cos ((n + 1 : Real) * alpha) /
    Real.cosh ((n + 1 : Real) * lam)


def sixVertexFourierRootDensityMajorant (lam : Real) (n : Nat) : Real :=
  2 * Real.exp (-lam) ^ (n + 1)

end
end StatMech.FrontierD

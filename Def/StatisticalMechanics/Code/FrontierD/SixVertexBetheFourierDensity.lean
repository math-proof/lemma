module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part5
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.ContinuousMap.Compact
open Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierDensity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexFourierRootDensityTerm (lam : Real) (n : Nat) (alpha : Real) : Real :=
  Real.cos ((n + 1 : Real) * alpha) /
    Real.cosh ((n + 1 : Real) * lam)


def sixVertexFourierRootDensityMajorant (lam : Real) (n : Nat) : Real :=
  2 * Real.exp (-lam) ^ (n + 1)

end
end StatMech.FrontierD

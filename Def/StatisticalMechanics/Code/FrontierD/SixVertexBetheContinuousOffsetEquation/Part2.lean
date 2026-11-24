module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetFourier.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffset.Part2
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetEquation


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def sixVertexOffsetConvolutionTerm
    (lam : Real) (n : Nat) (alpha : Real) : Real :=
  2 * Real.exp (-2 * ((n + 1 : Real) * lam)) *
    ((-1 : Real) ^ (n + 1) *
      Real.tanh ((n + 1 : Real) * lam) / (n + 1 : Real)) *
    Real.sin ((n + 1 : Real) * alpha)

end
end StatMech.FrontierD

module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLimit.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierConvolution.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part5
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronFourier.Part5
open Finset Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexAbelRootDensitySeriesTerm
    (lam r : Real) (n : Nat) : Real :=
  r ^ (n + 1) /
    ((n + 1 : Real) * Real.cosh ((n + 1 : Real) * lam))

end
end StatMech.FrontierD

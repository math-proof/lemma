module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLimit.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierConvolution.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part5
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronFourier
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

def sixVertexRegularizedRapidityB (lam epsilon : Real) : Real :=
  2 * (Real.cosh lam + 1) + epsilon

def sixVertexRegularizedRapidityDelta (lam epsilon : Real) : Real :=
  (2 * (Real.cosh lam + 1) + epsilon * Real.cosh lam) /
    sixVertexRegularizedRapidityB lam epsilon

def sixVertexRegularizedRapidityRadius (lam epsilon : Real) : Real :=
  Real.exp (-Real.arcosh
    (sixVertexRegularizedRapidityDelta lam epsilon))

end
end StatMech.FrontierD

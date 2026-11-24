module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetFourier.Part4
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetProfileRegularity


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetProfileRegularity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexOffsetRapidityLipschitzBound (lam : Real) : Real :=
  1 / (2 * Real.pi) +
    ∑' n : Nat, sixVertexOffsetCorrectionLipschitzTerm lam n

def sixVertexOffsetRapidityLipschitzNNReal (lam : Real) : NNReal :=
  Real.toNNReal (sixVertexOffsetRapidityLipschitzBound lam)

end
end StatMech.FrontierD

module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticStabilitySheet
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticCandidateSheet
open Finset Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticCandidateSheet.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexSymmetricBetheEigenvalueKernel
    {m : Nat} (c : Real) (q : Fin m → Real) : Real :=
  2 * ∏ j,
    (((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos (q j)) /
      (2 - 2 * Real.cos (q j)))

end
end StatMech.FrontierD

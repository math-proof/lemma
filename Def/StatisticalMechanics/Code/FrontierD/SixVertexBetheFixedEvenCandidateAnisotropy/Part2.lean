module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenCandidate.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeVandermonde.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedEvenCandidateAnisotropy
open Finset Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedEvenCandidateAnisotropy.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedEvenPositiveLimitingMNormSq (s k : Nat)
    (j : Fin (s + k + 1)) : Real :=
  1 / (2 - 2 * Real.cos (sixVertexFixedEvenPositiveLimitingRoot s k j))

end
end StatMech.FrontierD

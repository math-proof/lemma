module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeAnisotropyRoots.Part2
open Finset Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeAnisotropyRoots.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedChargeBetheRootAt_eq
    {c : Real} (hc : 2 < c) (r k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    sixVertexFixedChargeBetheRootAt r k j c =
      sixVertexFixedChargeBetheRoots hc r k j := by
  simp only [sixVertexFixedChargeBetheRootAt, dif_pos hc]


end
end StatMech.FrontierD

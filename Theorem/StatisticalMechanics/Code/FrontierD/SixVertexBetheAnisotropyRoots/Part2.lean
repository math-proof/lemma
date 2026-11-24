module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteRoots.Part2
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots
open Finset Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnisotropyRoots.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHalfFilledBetheRootAt_eq
    {c : Real} (hc : 2 < c) (k : Nat)
    (j : Fin ((k + 1) + (k + 1))) :
    sixVertexHalfFilledBetheRootAt k j c =
      sixVertexHalfFilledBetheRoots hc k j := by
  simp only [sixVertexHalfFilledBetheRootAt, dif_pos hc]


end
end StatMech.FrontierD

module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeAnisotropyRoots
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

@[simp] theorem sixVertexFixedChargeBetheComplementCount_eq (r k : Nat) :
    sixVertexFixedChargeBetheComplementCount r k = 3 * r + 2 * (k + 1) := by
  unfold sixVertexFixedChargeBetheComplementCount sixVertexFourWidth
  rw [sixVertexFixedChargeBetheParticleCount_eq]
  omega

theorem sixVertexFixedChargeBetheComplementCount_pos (r k : Nat) :
    0 < sixVertexFixedChargeBetheComplementCount r k := by
  rw [sixVertexFixedChargeBetheComplementCount_eq]
  omega


end
end StatMech.FrontierD

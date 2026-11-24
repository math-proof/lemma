module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeSpectralBranch
public import Mathlib.LinearAlgebra.Vandermonde
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeInfinityWave.Part3
open Finset Filter Matrix Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityWave.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedChargeLimitingWave_eq_det_alternant
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :
    sixVertexFixedChargeLimitingWave r k x =
      (sixVertexFixedChargeAlternantMatrix r k x).det := by
  rw [sixVertexFixedChargeLimitingWave_eq_alternant]
  rw [Matrix.det_apply']
  rfl


end
end StatMech.FrontierD

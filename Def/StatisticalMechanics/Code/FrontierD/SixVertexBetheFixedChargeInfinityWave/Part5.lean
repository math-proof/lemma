module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeSpectralBranch
public import Mathlib.LinearAlgebra.Vandermonde
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeInfinityWave.Part4
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

def sixVertexFixedChargeAlternantPoint (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k))
    (i : Fin (sixVertexFixedChargeBetheParticleCount r k)) : Complex :=
  sixVertexFixedChargeLimitingPhaseStep r k ^
    sixVertexFixedChargeAlternantExponent r k x i

end
end StatMech.FrontierD

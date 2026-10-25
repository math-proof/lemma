/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeSpectralBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedOddCandidateAnisotropy.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeVandermonde.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerronSpectralIsolation
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargeBetheRotatedRealWave
    {c : Real} (hc : 2 < c) (r k : Nat) (a : Complex) :
    SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k) -> Real :=
  fun x => (a * sixVertexCoordinateBetheWave c
    (sixVertexFixedChargeBetheRoots hc r k) x).re

end
end StatMech.FrontierD

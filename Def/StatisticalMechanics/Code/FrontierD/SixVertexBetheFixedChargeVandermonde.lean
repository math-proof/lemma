/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeVandermonde.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeAnisotropyRoots.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeVandermonde
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargeNormalizedAmplitude (r k : Nat) (c : Real)
    (sigma : Equiv.Perm (Fin (sixVertexFixedChargeBetheParticleCount r k))) :
    Complex :=
  (((Equiv.Perm.sign sigma : Int) : Complex)) *
    ∏ i, ∏ j ∈ Finset.Ioi i,
      sixVertexNormalizedBethePairFactor c
        (sixVertexBethePhase
          (sixVertexFixedChargeBetheRootAt r k (sigma i) c))
        (sixVertexBethePhase
          (sixVertexFixedChargeBetheRootAt r k (sigma j) c))

end
end StatMech.FrontierD

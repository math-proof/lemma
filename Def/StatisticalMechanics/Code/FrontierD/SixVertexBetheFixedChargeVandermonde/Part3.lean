/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeVandermonde.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeAnisotropyRoots.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeVandermonde.Part3
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargePairScaleProduct (r k : Nat) (c : Real) : Complex :=
  ∏ i : Fin (sixVertexFixedChargeBetheParticleCount r k),
    ∏ _j ∈ Finset.Ioi i, ((c ^ 2 - 2 : Real) : Complex)

end
end StatMech.FrontierD

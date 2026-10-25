/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeAnisotropyRoots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargeBetheComplementCount (r k : Nat) : Nat :=
  sixVertexFourWidth r k - sixVertexFixedChargeBetheParticleCount r k

end
end StatMech.FrontierD

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionThermodynamic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonFreeEnergy.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionThermodynamic.Part2
open Filter Topology Set
open scoped BigOperators Topology


namespace StatMech.FrontierA

noncomputable section

theorem cubicalSquareWilsonFreeEnergy_eq_disorderFreeEnergy
    {beta : Real} (hbeta : 0 < beta) (n : Nat) :
    cubicalSquareWilsonFreeEnergy beta n =
      cubicalSquareDisorderFreeEnergy beta n := by
  let L := n + 1
  have hL : 0 < L := by omega
  simpa [cubicalSquareWilsonFreeEnergy, cubicalSquareDisorderFreeEnergy, L]
    using neg_log_cubicalXYWilsonExpectation_eq_disorderFreeEnergy
    hL hL hL (0 : Fin (L + 1))
      (fun _ : CubicalPlaquette L L L => beta) (fun _ => hbeta)


end
end StatMech.FrontierA

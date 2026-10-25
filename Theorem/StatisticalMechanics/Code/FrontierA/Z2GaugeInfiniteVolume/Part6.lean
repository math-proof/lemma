/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalGluing.Part4
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume.Part5
open Filter Set Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem neg_log_cubicalPaddedWilsonExpectation_eq_disorderFreeEnergy
    {beta : Real} (hbeta : 0 < beta) {a b lx rx ly ry lz rz : Nat}
    (ha : 0 < a) (hb : 0 < b) (hz : 0 < lz + rz) :
    -Real.log (cubicalPaddedWilsonExpectation beta a b lx rx ly ry lz rz) =
      multibondDisorderFreeEnergy cubicalDualEnds
        (fun _ : CubicalPlaquette (lx + a + rx) (ly + b + ry) (lz + rz) =>
          gaugeDualCoupling beta)
        (cubicalPaddedXYSheet a b lx rx ly ry lz rz) := by
  rw [cubicalPaddedWilsonExpectation,
    ← gaugeSurfaceBoundary_cubicalPaddedXYSheet]
  exact neg_log_cubicalWilsonExpectation_eq_disorderFreeEnergy_of_surface
    (by omega) (by omega) hz (fun _ => beta) (fun _ => hbeta)
      (cubicalPaddedXYSheet a b lx rx ly ry lz rz)


end
end StatMech.FrontierA

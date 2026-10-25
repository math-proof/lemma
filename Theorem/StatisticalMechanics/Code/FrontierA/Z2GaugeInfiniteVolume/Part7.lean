/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalGluing.Part4
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume.Part6
open Filter Set Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem cubicalPaddedDisorderFreeEnergy_tendsto_infiniteVolume
    {beta : Real} (hbeta : 0 < beta) {a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (lx rx ly ry lz rz : Nat → Nat)
    (hlx : Tendsto lx atTop atTop) (hrx : Tendsto rx atTop atTop)
    (hly : Tendsto ly atTop atTop) (hry : Tendsto ry atTop atTop)
    (hlz : Tendsto lz atTop atTop) (hrz : Tendsto rz atTop atTop) :
    Tendsto (fun n => cubicalPaddedDisorderFreeEnergy beta a b
      (lx n) (rx n) (ly n) (ry n) (lz n) (rz n)) atTop
      (nhds (cubicalInfiniteVolumeWilsonFreeEnergy beta a b)) := by
  have hw := cubicalPaddedWilsonExpectation_tendsto_infiniteVolume
    hbeta a b lx rx ly ry lz rz hlx hrx hly hry hlz hrz
  have hpos := cubicalInfiniteVolumeWilsonExpectation_pos hbeta a b
  have hlog := (Real.continuousAt_log hpos.ne').tendsto.comp hw
  have hneg : Tendsto (fun n =>
      -Real.log (cubicalPaddedWilsonExpectation beta a b
        (lx n) (rx n) (ly n) (ry n) (lz n) (rz n))) atTop
      (nhds (cubicalInfiniteVolumeWilsonFreeEnergy beta a b)) := by
    simpa [cubicalInfiniteVolumeWilsonFreeEnergy] using hlog.neg
  apply hneg.congr'
  filter_upwards [hlz.eventually (eventually_ge_atTop 1)] with n hn
  simpa [cubicalPaddedDisorderFreeEnergy] using
    (neg_log_cubicalPaddedWilsonExpectation_eq_disorderFreeEnergy
    (a := a) (b := b) (lx := lx n) (rx := rx n)
    (ly := ly n) (ry := ry n) (lz := lz n) (rz := rz n)
    hbeta ha hb (by omega))

end
end StatMech.FrontierA

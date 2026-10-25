/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSSchedule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceScheduledCapstone
import Mathlib.Data.Nat.Choose.Bounds
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidencePIMSSchedule.Part4
open Filter Topology MeasureTheory


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_fkRectFixedChargeFreeOneArm_zero_of_percolation_zero
    {q : Real} (hq : 1 ≤ q) (r : Nat)
    (hperc :
      let mu := (FK.freeInfiniteVolume 2
        (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
        (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
        (zero_lt_one.trans_le hq) :
          MeasureTheory.Measure (ConfigSpace
            (Sym2 (StatMech.Lattice.Site 2))))
      mu.real (Percolation.percolationEvent 2) = 0) :
    Tendsto (fkRectFixedChargeFreeOneArm hq r) atTop (nhds 0) := by
  let mu := (FK.freeInfiniteVolume 2
    (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
    (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
    (zero_lt_one.trans_le hq) :
      MeasureTheory.Measure (ConfigSpace
        (Sym2 (StatMech.Lattice.Site 2))))
  have hbox :=
    fkRect_boxBdryConnEvent_real_tendsto_zero_of_percolation_zero
      mu hperc
  have hradius : Tendsto (fun k =>
      (fkRectFixedChargeVerticalFamily r k 0).width - 2) atTop atTop := by
    refine tendsto_atTop.2 (fun N => ?_)
    filter_upwards [eventually_ge_atTop N] with k hk
    simp only [fkRectFixedChargeVerticalFamily_width]
    omega
  simpa [fkRectFixedChargeFreeOneArm, mu] using hbox.comp hradius

set_option maxHeartbeats 800000 in


theorem
    fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_freePIMS_fourCopy
    {q xiInv : Real} (hq : 4 < q) (r : Nat) (hr : 2 ≤ r)
    (hperc :
      let mu := (FK.freeInfiniteVolume 2
        (fkRectCriticalP_pos (by linarith : 0 < q))
        (fkRectCriticalP_lt_one (by linarith : 0 < q))
        (by linarith : 0 < q) :
          MeasureTheory.Measure (ConfigSpace
            (Sym2 (StatMech.Lattice.Site 2))))
      mu.real (Percolation.percolationEvent 2) = 0)
    (hwind : ∀ m : Nat → Nat,
      (∀ k, fkRectBoundaryIncidencePIMSHeightLower q r k ≤ m k) →
      Tendsto (fun k =>
        -Real.log
            (fkRectCriticalWindingTailMass
              (fkRectFixedChargeVerticalFamily r k (m k)) q r) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds (((r - 1 : Nat) : Real) * xiInv)))
    (hfourCopy : ∀ m : Nat → Nat,
      (∀ k, fkRectBoundaryIncidencePIMSHeightLower q r k ≤ m k) →
      Tendsto (fun k =>
        fkRectFourCopyShareCost
            (fkRectFixedChargeVerticalFamily r k (m k)) q /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds 0)) :
    ((r - 1 : Nat) : Real) * xiInv ≤
      (r : Real) * fkQgt4SixVertexGapRate q := by
  let hq1 : 1 ≤ q := by linarith
  let c := FK.cFE (fkRectCriticalP q) q
  let p := fkRectFixedChargeFreeOneArm hq1 r
  let depth := fkRectPIMSDecayDepth (c / 4) p
  let threshold : (Nat → Nat) → Nat → Nat := fun m k =>
    fkRectPIMSSublinearThreshold (depth k)
      (fkRectFixedChargeVerticalFamily r k (m k)).height
  have hc0 : 0 < c := by
    exact FK.cFE_pos
      (fkRectCriticalP_pos (by linarith : 0 < q))
      (fkRectCriticalP_lt_one (by linarith : 0 < q)) (by linarith)
  have hc1 : c ≤ 1 := fkRectCritical_cFE_le_one hq1
  have hp0 : ∀ k, 0 ≤ p k := fun _ => measureReal_nonneg
  have hp1 : ∀ k, p k ≤ 1 := fun _ => measureReal_le_one
  have hp : Tendsto p atTop (nhds 0) := by
    exact tendsto_fkRectFixedChargeFreeOneArm_zero_of_percolation_zero
      hq1 r hperc
  have scheduled (m : Nat → Nat)
      (hm : ∀ k, fkRectBoundaryIncidencePIMSHeightLower q r k ≤ m k) :=
    fkRect_pimsDecay_scheduled_binomialSmallness hc0 hc1 p hp0 hp1 hp
      (fun k => (fkRectFixedChargeVerticalFamily r k (m k)).width)
      (fun k => (fkRectFixedChargeVerticalFamily r k (m k)).height)
      (fun k => (fkRectFixedChargeVerticalFamily r k (m k)).height_pos)
      (fun k => by
        change fkRectPIMSHeightLower c
            (fkRectFixedChargeVerticalFamily r k (m k)).width ≤
          (fkRectFixedChargeVerticalFamily r k (m k)).height
        simp only [fkRectFixedChargeVerticalFamily_width,
          fkRectFixedChargeVerticalFamily_height]
        have hm' := hm k
        dsimp [fkRectBoundaryIncidencePIMSHeightLower] at hm'
        dsimp [c]
        omega)
  apply
    fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_boundaryIncidenceTail_fourCopy
      hq r hr (fkRectBoundaryIncidencePIMSHeightLower q r) threshold hwind
  · intro m hm k
    simpa [threshold, depth, p, c, fkRectFixedChargeFreeOneArm] using
      (scheduled m hm).1 k
  · intro m hm
    have hupper : Tendsto (fun k : Nat => (1 : Real) / k) atTop (nhds 0) :=
      (tendsto_natCast_atTop_atTop (R := Real)).const_div_atTop 1
    apply squeeze_zero' (g := fun k : Nat => (1 : Real) / k)
    · filter_upwards [] with k
      positivity
    · filter_upwards [eventually_ge_atTop 1] with k hk
      let W := (fkRectFixedChargeVerticalFamily r k (m k)).width
      let H := (fkRectFixedChargeVerticalFamily r k (m k)).height
      have hm' := hm k
      have hmul : k * W ≤ m k := by
        dsimp [fkRectBoundaryIncidencePIMSHeightLower] at hm'
        exact (Nat.le_add_right _ _).trans hm'
      have hkreal : (0 : Real) < k := by exact_mod_cast hk
      have hHreal : (0 : Real) < H := by
        exact_mod_cast (fkRectFixedChargeVerticalFamily r k (m k)).height_pos
      apply (div_le_div_iff₀ hHreal hkreal).2
      have hnat : W * k ≤ H := by
        have hmk : W * k ≤ m k := by
          simpa [Nat.mul_comm] using hmul
        exact hmk.trans (by
          dsimp [H]
          omega)
      change (W : Real) * (k : Real) ≤ 1 * (H : Real)
      norm_num
      exact_mod_cast hnat
    · exact hupper
  · intro m hm
    simpa [threshold, depth, p, c] using (scheduled m hm).2
  · intro m hm
    refine tendsto_atTop.2 (fun N => ?_)
    filter_upwards [eventually_ge_atTop N] with k hk
    have hm' := hm k
    dsimp [fkRectBoundaryIncidencePIMSHeightLower] at hm'
    have hmk : k ≤ m k := by
      have hw : 1 ≤ (fkRectFixedChargeVerticalFamily r k 0).width :=
        (fkRectFixedChargeVerticalFamily r k 0).width_pos
      exact (Nat.le_mul_of_pos_right k hw).trans
        ((Nat.le_add_right _ _).trans hm')
    simp only [fkRectFixedChargeVerticalFamily_height]
    omega
  · exact hfourCopy

end
end StatMech.FrontierD

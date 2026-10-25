/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSSchedule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceScheduledCapstone
import Mathlib.Data.Nat.Choose.Bounds
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidencePIMSSchedule.Part3
open Filter Topology MeasureTheory


namespace StatMech.FrontierD

noncomputable section

theorem fkRectPIMSHeightLower_width_le
    (c : Real) (width : Nat) :
    width ≤ fkRectPIMSHeightLower c width :=
  le_max_left _ _


theorem fkRectPIMSHeightLower_domination
    {c : Real} (hc0 : 0 < c) (width height : Nat)
    (hheight : fkRectPIMSHeightLower c width ≤ height) :
    (c / 2) ^ height ≤ c ^ (2 * width + height) / 2 := by
  let first := Nat.find (exists_fkRectPIMSHeightDominating c width)
  have hfirst : first ≤ height := by
    exact (le_max_right width first).trans hheight
  have hbase : 2 / c ^ (2 * width) ≤ (2 : Real) ^ first :=
    Nat.find_spec (exists_fkRectPIMSHeightDominating c width)
  have htwo : (2 : Real) ^ first ≤ (2 : Real) ^ height := by
    exact pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2) hfirst
  have hcwidth : 0 < c ^ (2 * width) := pow_pos hc0 _
  have hmul : (2 : Real) ≤ (2 : Real) ^ height * c ^ (2 * width) := by
    exact (div_le_iff₀ hcwidth).mp (hbase.trans htwo)
  have hcHeight : 0 ≤ c ^ height := (pow_pos hc0 _).le
  have hcross := mul_le_mul_of_nonneg_right hmul hcHeight
  have htwoPow : 0 < (2 : Real) ^ height := pow_pos (by norm_num) _
  rw [div_pow, pow_add]
  apply (div_le_div_iff₀ htwoPow (by norm_num : (0 : Real) < 2)).2
  calc
    c ^ height * 2 = 2 * c ^ height := by ring
    _ ≤ ((2 : Real) ^ height * c ^ (2 * width)) * c ^ height := hcross
    _ = (c ^ (2 * width) * c ^ height) * 2 ^ height := by ring


theorem fkRect_pimsDecay_scheduled_binomialSmallness
    {c : Real} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (p : Nat → Real) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (hp : Tendsto p atTop (nhds 0))
    (width height : Nat → Nat)
    (hheight_pos : ∀ k, 0 < height k)
    (hheightLower : ∀ k,
      fkRectPIMSHeightLower c (width k) ≤ height k) :
    let depth := fkRectPIMSDecayDepth (c / 4) p
    let threshold := fun k =>
      fkRectPIMSSublinearThreshold (depth k) (height k)
    (∀ k, Nat.choose (height k) (threshold k + 1) *
        (p k) ^ (threshold k + 1) ≤
          c ^ (2 * width k + height k) / 2) ∧
      Tendsto (fun k => (threshold k : Real) / height k)
        atTop (nhds 0) := by
  dsimp only
  let depth := fkRectPIMSDecayDepth (c / 4) p
  have hc4 : 0 < c / 4 := by positivity
  have hdepth : Tendsto depth atTop atTop :=
    tendsto_fkRectPIMSDecayDepth_atTop hc4 hp
  constructor
  · intro k
    change Nat.choose (height k)
        (fkRectPIMSSublinearThreshold (depth k) (height k) + 1) *
          p k ^ (fkRectPIMSSublinearThreshold (depth k) (height k) + 1) ≤
        c ^ (2 * width k + height k) / 2
    by_cases hzero : depth k = 0
    · simp [fkRectPIMSSublinearThreshold, hzero]
      positivity
    · rw [fkRectPIMSSublinearThreshold, if_neg hzero]
      exact fkRect_choose_mul_pow_le_finiteEnergy_of_pimsDepth
        (hp0 k) hc0 hc1 (width k) (height k) (depth k)
        (Nat.pos_of_ne_zero hzero)
        (fkRectPIMSDecayDepth_spec hp1 k)
        (fkRectPIMSHeightLower_domination hc0 _ _ (hheightLower k))
  · exact tendsto_fkRectPIMSSublinearThreshold_div_height_zero
      depth height hdepth hheight_pos


theorem fkRect_boxBdryConnEvent_real_tendsto_zero_of_percolation_zero
    (mu : MeasureTheory.Measure
      (ConfigSpace (Sym2 (StatMech.Lattice.Site 2))))
    [MeasureTheory.IsFiniteMeasure mu]
    (hperc : mu.real (Percolation.percolationEvent 2) = 0) :
    Tendsto (fun n => mu.real (FK.boxBdryConnEvent 2 n))
      atTop (nhds 0) := by
  simpa [hperc] using
    (FK.boxBdryConnEvent_real_tendsto_percolation (d := 2) mu)


end
end StatMech.FrontierD

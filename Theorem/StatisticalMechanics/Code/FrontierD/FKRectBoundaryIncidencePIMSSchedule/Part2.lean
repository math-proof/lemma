/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSSchedule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceScheduledCapstone
import Mathlib.Data.Nat.Choose.Bounds
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidencePIMSSchedule.Part2
open Filter Topology MeasureTheory


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_fkRectPIMSSublinearThreshold_div_height_zero
    (depth height : Nat → Nat)
    (hdepth : Tendsto depth atTop atTop)
    (hheight_pos : ∀ k, 0 < height k) :
    Tendsto (fun k =>
      (fkRectPIMSSublinearThreshold (depth k) (height k) : Real) /
        height k) atTop (nhds 0) := by
  have hdepthReal : Tendsto (fun k => (depth k : Real)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hdepth
  have hupper : Tendsto (fun k => (1 : Real) / depth k)
      atTop (nhds 0) := hdepthReal.const_div_atTop 1
  apply squeeze_zero' (g := fun k => (1 : Real) / depth k)
  · filter_upwards [] with k
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [tendsto_atTop.1 hdepth 1] with k hk
    have hdpos : 0 < depth k := by omega
    have hdne : depth k ≠ 0 := Nat.ne_of_gt hdpos
    rw [fkRectPIMSSublinearThreshold, if_neg hdne]
    have hcast : ((height k / depth k : Nat) : Real) ≤
        (height k : Real) / depth k := Nat.cast_div_le
    have hhreal : (0 : Real) < height k := by exact_mod_cast hheight_pos k
    calc
      ((height k / depth k : Nat) : Real) / height k ≤
          ((height k : Real) / depth k) / height k :=
        div_le_div_of_nonneg_right hcast hhreal.le
      _ = (1 : Real) / depth k := by
        field_simp
  · exact hupper


theorem fkRect_choose_mul_pow_le_finiteEnergy_of_pimsDepth
    {p c : Real} (hp0 : 0 ≤ p) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (width height depth : Nat) (hdepth : 0 < depth)
    (hpdepth : p ≤ (c / 4) ^ depth)
    (hheight : (c / 2) ^ height ≤ c ^ (2 * width + height) / 2) :
    Nat.choose height (height / depth + 1) * p ^ (height / depth + 1) ≤
      c ^ (2 * width + height) / 2 := by
  have ha0 : 0 ≤ c / 4 := by positivity
  have ha1 : c / 4 ≤ 1 := by linarith
  have hexponent : height ≤ depth * (height / depth + 1) := by
    have hmod := Nat.mod_lt height hdepth
    calc
      height = depth * (height / depth) + height % depth :=
        (Nat.div_add_mod height depth).symm
      _ ≤ depth * (height / depth) + depth := Nat.add_le_add_left hmod.le _
      _ = depth * (height / depth + 1) := by ring
  have hprob : p ^ (height / depth + 1) ≤ (c / 4) ^ height := by
    calc
      p ^ (height / depth + 1) ≤
          ((c / 4) ^ depth) ^ (height / depth + 1) := by
        gcongr
      _ = (c / 4) ^ (depth * (height / depth + 1)) := by
        rw [pow_mul]
      _ ≤ (c / 4) ^ height :=
        pow_le_pow_of_le_one ha0 ha1 hexponent
  have hchoose : (Nat.choose height (height / depth + 1) : Real) ≤
      (2 : Real) ^ height := by
    exact_mod_cast Nat.choose_le_two_pow height (height / depth + 1)
  calc
    Nat.choose height (height / depth + 1) *
          p ^ (height / depth + 1) ≤
        (2 : Real) ^ height * (c / 4) ^ height :=
      mul_le_mul hchoose hprob (pow_nonneg hp0 _) (pow_nonneg (by positivity) _)
    _ = (c / 2) ^ height := by
      rw [← mul_pow]
      congr 1
      ring
    _ ≤ c ^ (2 * width + height) / 2 := hheight


theorem exists_fkRectPIMSHeightDominating
    (c : Real) (width : Nat) :
    ∃ height : Nat, 2 / c ^ (2 * width) ≤ (2 : Real) ^ height := by
  have ht : Tendsto (fun height : Nat => (2 : Real) ^ height)
      atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  exact (tendsto_atTop.1 ht (2 / c ^ (2 * width))).exists


end
end StatMech.FrontierD

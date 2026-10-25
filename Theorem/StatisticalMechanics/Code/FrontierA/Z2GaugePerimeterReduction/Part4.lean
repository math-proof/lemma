/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugePerimeterReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeThermodynamicReduction.Part2
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugePerimeterReduction.Part4
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

theorem gaugePerimeterPenalty_pos {R : Real} (hR0 : 0 < R) (hR1 : R < 1) :
    0 < gaugePerimeterPenalty R := by
  have hone : 0 < 1 - R := sub_pos.mpr hR1
  have hlt : 1 - R < 1 := by linarith
  have hlog : Real.log (1 - R) < 0 := (Real.log_neg hone hlt)
  exact div_pos (neg_pos.mpr hlog) hR0


theorem exp_neg_gaugePerimeterPenalty_mul (R : Real) (hR0 : 0 < R)
    (hR1 : R < 1) :
    Real.exp (-(gaugePerimeterPenalty R) * R) = 1 - R := by
  have hne : R ≠ 0 := ne_of_gt hR0
  have hone : 0 < 1 - R := sub_pos.mpr hR1
  rw [gaugePerimeterPenalty]
  have hexp : -(-Real.log (1 - R) / R) * R = Real.log (1 - R) := by
    field_simp
  rw [hexp, Real.exp_log hone]


theorem exp_neg_gaugePerimeterPenalty_mul_le_one_sub
    {R r : Real} (hR0 : 0 < R) (hR1 : R < 1)
    (hr0 : 0 <= r) (hrR : r <= R) :
    Real.exp (-(gaugePerimeterPenalty R) * r) <= 1 - r := by
  let t := r / R
  have ht0 : 0 <= t := div_nonneg hr0 hR0.le
  have ht1 : t <= 1 := (div_le_one hR0).2 hrR
  have hRm : 0 < 1 - R := sub_pos.mpr hR1
  have hconcave := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1 : Real) ∈ Set.Ioi 0 by norm_num)
    (show 1 - R ∈ Set.Ioi 0 by exact hRm)
    (sub_nonneg.mpr ht1) ht0 (by simp)
  have harg : 1 - t + t * (1 - R) = 1 - r := by
    dsimp [t]
    field_simp
    ring
  have hlog : t * Real.log (1 - R) <= Real.log (1 - r) := by
    have hc : t * Real.log (1 - R) <=
        Real.log (1 - t + t * (1 - R)) := by
      simpa [smul_eq_mul, Real.log_one] using hconcave
    rwa [harg] at hc
  have hr1 : 0 < 1 - r := by linarith
  rw [← Real.exp_log hr1]
  apply (Real.exp_le_exp).2
  calc
    -(gaugePerimeterPenalty R) * r = t * Real.log (1 - R) := by
      dsimp [gaugePerimeterPenalty, t]
      field_simp
    _ <= Real.log (1 - r) := hlog


theorem exp_neg_gaugePerimeterPenalty_mul_sum_le_prod_one_sub
    {I : Type*} {R : Real} (hR0 : 0 < R) (hR1 : R < 1)
    (s : Finset I) (r : I -> Real)
    (hr0 : forall i : I, i ∈ s -> 0 <= r i)
    (hrR : forall i : I, i ∈ s -> r i <= R) :
    Real.exp (-(gaugePerimeterPenalty R) * (∑ i ∈ s, r i)) <=
      ∏ i ∈ s, (1 - r i) := by
  classical
  have hsum : -(gaugePerimeterPenalty R) * (∑ i ∈ s, r i) =
      ∑ i ∈ s, (-(gaugePerimeterPenalty R) * r i) := by
    rw [Finset.mul_sum]
  rw [hsum, Real.exp_sum]
  exact Finset.prod_le_prod
    (fun i hi => (Real.exp_pos _).le)
    (fun i hi => exp_neg_gaugePerimeterPenalty_mul_le_one_sub
      hR0 hR1 (hr0 i hi) (hrR i hi))


theorem gauge_perimeterLaw_of_product_and_sum_bounds
    {I : Type*} {R C perimeter wilson : Real}
    (hR0 : 0 < R) (hR1 : R < 1)
    (s : Finset I) (r : I -> Real)
    (hr0 : forall i : I, i ∈ s -> 0 <= r i)
    (hrR : forall i : I, i ∈ s -> r i <= R)
    (hproduct : (∏ i ∈ s, (1 - r i)) <= wilson)
    (hsum : (∑ i ∈ s, r i) <= C * perimeter) :
    Real.exp (-(gaugePerimeterPenalty R * C) * perimeter) <= wilson := by
  classical
  have hg : 0 <= gaugePerimeterPenalty R :=
    (gaugePerimeterPenalty_pos hR0 hR1).le
  have hscale :
      -(gaugePerimeterPenalty R) * (C * perimeter) <=
        -(gaugePerimeterPenalty R) * (∑ i ∈ s, r i) := by
    exact mul_le_mul_of_nonpos_left hsum (neg_nonpos.mpr hg)
  have hexp :
      Real.exp (-(gaugePerimeterPenalty R * C) * perimeter) <=
        Real.exp (-(gaugePerimeterPenalty R) * (∑ i ∈ s, r i)) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_mul, mul_assoc] using hscale
  exact hexp.trans <|
    (exp_neg_gaugePerimeterPenalty_mul_sum_le_prod_one_sub
      hR0 hR1 s r hr0 hrR).trans hproduct


theorem fk_perimeterLaw_of_cylinder_bridge_and_sum_bound
    {V I : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q R C perimeter wilson : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hR0 : 0 < R) (hR1 : R < 1)
    (s : Finset I) (x y : I -> V)
    (hR : forall i, i ∈ s -> FK.twoPointFun G p q (x i) (y i) <= R)
    (hcylinder :
      finiteEventMass (FK.fkProb G p q)
          (finiteEventInter s (fun i => fkDisconnEvent G (x i) (y i))) <=
        wilson)
    (hsum : (∑ i ∈ s, FK.twoPointFun G p q (x i) (y i)) <=
      C * perimeter) :
    Real.exp (-(gaugePerimeterPenalty R * C) * perimeter) <= wilson := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  apply gauge_perimeterLaw_of_product_and_sum_bounds
    hR0 hR1 s (fun i => FK.twoPointFun G p q (x i) (y i))
  · intro i _
    exact FK.twoPointFun_nonneg G hp hp1 hq0 (x i) (y i)
  · exact hR
  · exact (fk_finite_pair_nonconnection_product_bound
      G hp hp1 hq s x y).trans hcylinder
  · exact hsum

end
end StatMech.FrontierA

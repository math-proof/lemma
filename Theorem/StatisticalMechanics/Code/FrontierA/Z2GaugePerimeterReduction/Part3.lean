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
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugePerimeterReduction.Part3
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

theorem fkDisconnEvent_decreasing {V : Type*} (G : SimpleGraph V)
    (x y : V) : IsDecreasing (fkDisconnEvent G x y) :=
  (FK.connEvent_isIncreasing G x y).compl


theorem finiteEventMass_fkDisconnEvent_eq_one_sub_twoPointFun
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (x y : V) :
    finiteEventMass (FK.fkProb G p q) (fkDisconnEvent G x y) =
      1 - FK.twoPointFun G p q x y := by
  classical
  unfold finiteEventMass FK.twoPointFun fkDisconnEvent
  calc
    (∑ omega, FK.fkProb G p q omega *
        (FK.connEvent G x y)ᶜ.indicator (fun _ => (1 : Real)) omega) =
        ∑ omega, FK.fkProb G p q omega *
          (1 - (FK.connEvent G x y).indicator (fun _ => (1 : Real)) omega) := by
      apply Finset.sum_congr rfl
      intro omega _
      congr 1
      by_cases homega : omega ∈ FK.connEvent G x y <;>
        simp [homega]
    _ = (∑ omega, FK.fkProb G p q omega) -
        ∑ omega, FK.fkProb G p q omega *
          (FK.connEvent G x y).indicator (fun _ => (1 : Real)) omega := by
      simp_rw [mul_sub, mul_one]
      rw [Finset.sum_sub_distrib]
    _ = 1 - ∑ omega, FK.fkProb G p q omega *
          (FK.connEvent G x y).indicator (fun _ => (1 : Real)) omega := by
      rw [FK.fkProb_sum_eq_one G hp hp1 hq]


theorem fk_finite_pair_nonconnection_product_bound
    {V I : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (s : Finset I) (x y : I -> V) :
    (∏ i ∈ s, (1 - FK.twoPointFun G p q (x i) (y i))) <=
      finiteEventMass (FK.fkProb G p q)
        (finiteEventInter s (fun i => fkDisconnEvent G (x i) (y i))) := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have h := fkg_inequality_finite_decreasing_events
    (fun omega => FK.fkProb_nonneg G hp hp1 hq0 omega)
    (FK.fkProb_sum_eq_one G hp hp1 hq0)
    (FK.fkProb_FKGLatticeCondition G hp hp1 hq)
    s (fun i => fkDisconnEvent G (x i) (y i))
    (fun i _ => fkDisconnEvent_decreasing G (x i) (y i))
  simpa only [finiteEventMass_fkDisconnEvent_eq_one_sub_twoPointFun
    G hp hp1 hq0] using h


end
end StatMech.FrontierA

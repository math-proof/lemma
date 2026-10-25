/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTransform.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeHighTemp
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTransform.Part3
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

section LocalGauge

variable {Q E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]


omit [Fintype E] [Fintype P] [DecidableEq P] in


theorem plaquetteSpin_localGaugeTransform_eq
    (incidence : P -> Finset E) (star : Q -> Finset E)
    (hcomplex : HasEvenPlaquetteStarIncidence incidence star)
    (v : Q) (omega : GaugeConfig E) (p : P) :
    plaquetteSpin incidence (localGaugeTransform star v omega) p =
      plaquetteSpin incidence omega p := by
  rw [plaquetteSpin_localGaugeTransform]
  rw [(hcomplex v p).neg_one_pow]
  simp

omit [Fintype E] [DecidableEq P] in

theorem gaugeAction_localGaugeTransform_eq
    (incidence : P -> Finset E) (star : Q -> Finset E)
    (hcomplex : HasEvenPlaquetteStarIncidence incidence star)
    (K : P -> ℝ) (v : Q) (omega : GaugeConfig E) :
    gaugeAction incidence K (localGaugeTransform star v omega) =
      gaugeAction incidence K omega := by
  unfold gaugeAction
  apply Finset.sum_congr rfl
  intro p _
  rw [plaquetteSpin_localGaugeTransform_eq incidence star hcomplex]

omit [Fintype E] [DecidableEq P] in

theorem gaugeWeight_localGaugeTransform_eq
    (incidence : P -> Finset E) (star : Q -> Finset E)
    (hcomplex : HasEvenPlaquetteStarIncidence incidence star)
    (K : P -> ℝ) (v : Q) (omega : GaugeConfig E) :
    gaugeWeight incidence K (localGaugeTransform star v omega) =
      gaugeWeight incidence K omega := by
  unfold gaugeWeight
  rw [gaugeAction_localGaugeTransform_eq incidence star hcomplex]

omit [Fintype E] [Fintype P] [DecidableEq P] in


theorem wilsonSpin_localGaugeTransform (star : Q -> Finset E) (v : Q)
    (L : Finset E) (omega : GaugeConfig E) :
    wilsonSpin L (localGaugeTransform star v omega) =
      (-1 : ℝ) ^ (L ∩ star v).card * wilsonSpin L omega := by
  unfold wilsonSpin
  simp_rw [gaugeEdgeSpin_localGaugeTransform star v omega]
  rw [Finset.prod_mul_distrib, prod_star_sign]


end LocalGauge
end StatMech.FrontierA

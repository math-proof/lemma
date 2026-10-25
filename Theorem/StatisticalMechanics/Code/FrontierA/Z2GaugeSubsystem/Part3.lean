/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSubsystem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeGKS.Part2
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeSubsystem.Part3
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

@[simp] theorem extendGaugeCoupling_apply {Psmall Pbig : Type*}
    (f : Psmall ↪ Pbig) (K : Psmall → Real) (p : Psmall) :
    extendGaugeCoupling f K (f p) = K p := by
  simp [extendGaugeCoupling]

variable {Esmall Ebig Psmall Pbig : Type*}
  [Fintype Esmall] [DecidableEq Esmall] [Fintype Ebig] [DecidableEq Ebig]
  [Fintype Psmall] [DecidableEq Psmall] [Fintype Pbig] [DecidableEq Pbig]

theorem plaquetteSpin_gaugeConfigSplitEquiv
    (incidenceSmall : Psmall → Finset Esmall)
    (incidenceBig : Pbig → Finset Ebig)
    (eEmb : Esmall ↪ Ebig) (pEmb : Psmall ↪ Pbig)
    (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
    (sigma : GaugeConfig Esmall)
    (tau : {e : Ebig // e ∉ Set.range eEmb} → Bool) (p : Psmall) :
    plaquetteSpin incidenceBig (gaugeConfigSplitEquiv eEmb (sigma, tau)) (pEmb p) =
      plaquetteSpin incidenceSmall sigma p := by
  unfold plaquetteSpin
  rw [hinc, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro e _
  simp [gaugeEdgeSpin]

theorem gaugeAction_extendGaugeCoupling_gaugeConfigSplitEquiv
    (incidenceSmall : Psmall → Finset Esmall)
    (incidenceBig : Pbig → Finset Ebig)
    (eEmb : Esmall ↪ Ebig) (pEmb : Psmall ↪ Pbig)
    (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
    (K : Psmall → Real) (sigma : GaugeConfig Esmall)
    (tau : {e : Ebig // e ∉ Set.range eEmb} → Bool) :
    gaugeAction incidenceBig (extendGaugeCoupling pEmb K)
        (gaugeConfigSplitEquiv eEmb (sigma, tau)) =
      gaugeAction incidenceSmall K sigma := by
  unfold gaugeAction
  rw [← (embeddingSplitEquiv pEmb).sum_comp, Fintype.sum_sum_type]
  simp [extendGaugeCoupling,
    plaquetteSpin_gaugeConfigSplitEquiv incidenceSmall incidenceBig eEmb pEmb hinc]

theorem gaugeWeight_extendGaugeCoupling_gaugeConfigSplitEquiv
    (incidenceSmall : Psmall → Finset Esmall)
    (incidenceBig : Pbig → Finset Ebig)
    (eEmb : Esmall ↪ Ebig) (pEmb : Psmall ↪ Pbig)
    (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
    (K : Psmall → Real) (sigma : GaugeConfig Esmall)
    (tau : {e : Ebig // e ∉ Set.range eEmb} → Bool) :
    gaugeWeight incidenceBig (extendGaugeCoupling pEmb K)
        (gaugeConfigSplitEquiv eEmb (sigma, tau)) =
      gaugeWeight incidenceSmall K sigma := by
  unfold gaugeWeight
  rw [gaugeAction_extendGaugeCoupling_gaugeConfigSplitEquiv
    incidenceSmall incidenceBig eEmb pEmb hinc]

theorem wilsonSpin_gaugeConfigSplitEquiv_map
    (eEmb : Esmall ↪ Ebig) (L : Finset Esmall)
    (sigma : GaugeConfig Esmall)
    (tau : {e : Ebig // e ∉ Set.range eEmb} → Bool) :
    wilsonSpin (L.map eEmb) (gaugeConfigSplitEquiv eEmb (sigma, tau)) =
      wilsonSpin L sigma := by
  unfold wilsonSpin
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro e _
  simp [gaugeEdgeSpin]

theorem gaugePartition_extendGaugeCoupling
    (incidenceSmall : Psmall → Finset Esmall)
    (incidenceBig : Pbig → Finset Ebig)
    (eEmb : Esmall ↪ Ebig) (pEmb : Psmall ↪ Pbig)
    (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
    (K : Psmall → Real) :
    gaugePartition incidenceBig (extendGaugeCoupling pEmb K) =
      Fintype.card ({e : Ebig // e ∉ Set.range eEmb} → Bool) *
        gaugePartition incidenceSmall K := by
  unfold gaugePartition
  rw [← (gaugeConfigSplitEquiv eEmb).sum_comp, Fintype.sum_prod_type]
  simp_rw [gaugeWeight_extendGaugeCoupling_gaugeConfigSplitEquiv
    incidenceSmall incidenceBig eEmb pEmb hinc]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]

theorem gaugeWilsonNumerator_extendGaugeCoupling
    (incidenceSmall : Psmall → Finset Esmall)
    (incidenceBig : Pbig → Finset Ebig)
    (eEmb : Esmall ↪ Ebig) (pEmb : Psmall ↪ Pbig)
    (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
    (K : Psmall → Real) (L : Finset Esmall) :
    gaugeWilsonNumerator incidenceBig (extendGaugeCoupling pEmb K) (L.map eEmb) =
      Fintype.card ({e : Ebig // e ∉ Set.range eEmb} → Bool) *
        gaugeWilsonNumerator incidenceSmall K L := by
  unfold gaugeWilsonNumerator
  rw [← (gaugeConfigSplitEquiv eEmb).sum_comp, Fintype.sum_prod_type]
  simp_rw [gaugeWeight_extendGaugeCoupling_gaugeConfigSplitEquiv
    incidenceSmall incidenceBig eEmb pEmb hinc,
    wilsonSpin_gaugeConfigSplitEquiv_map]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]


theorem gaugeWilsonExpectation_extendGaugeCoupling
    (incidenceSmall : Psmall → Finset Esmall)
    (incidenceBig : Pbig → Finset Ebig)
    (eEmb : Esmall ↪ Ebig) (pEmb : Psmall ↪ Pbig)
    (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
    (K : Psmall → Real) (L : Finset Esmall) :
    gaugeWilsonExpectation incidenceBig (extendGaugeCoupling pEmb K) (L.map eEmb) =
      gaugeWilsonExpectation incidenceSmall K L := by
  unfold gaugeWilsonExpectation
  rw [gaugeWilsonNumerator_extendGaugeCoupling incidenceSmall incidenceBig
      eEmb pEmb hinc,
    gaugePartition_extendGaugeCoupling incidenceSmall incidenceBig eEmb pEmb hinc]
  have hcard :
      (Fintype.card ({e : Ebig // e ∉ Set.range eEmb} → Bool) : Real) ≠ 0 := by
    positivity
  exact mul_div_mul_left _ _ hcard

end
end StatMech.FrontierA

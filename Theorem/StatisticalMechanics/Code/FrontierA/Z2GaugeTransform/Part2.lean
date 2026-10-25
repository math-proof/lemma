/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTransform.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeHighTemp
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTransform.Part2
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

section LocalGauge

variable {Q E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]


omit [Fintype E] [Fintype P] [DecidableEq P] in

theorem gaugeEdgeSpin_localGaugeTransform (star : Q -> Finset E) (v : Q)
    (omega : GaugeConfig E) (e : E) :
    gaugeEdgeSpin (localGaugeTransform star v omega) e =
      (if e ∈ star v then (-1 : ℝ) else 1) * gaugeEdgeSpin omega e := by
  by_cases he : e ∈ star v <;>
    cases hspin : omega e <;>
      simp [localGaugeTransform, gaugeEdgeSpin, he, hspin]

omit [Fintype E] [Fintype P] [DecidableEq P] in


theorem prod_star_sign (star : Q -> Finset E) (v : Q) (A : Finset E) :
    (∏ e ∈ A, if e ∈ star v then (-1 : ℝ) else 1) =
      (-1 : ℝ) ^ (A ∩ star v).card := by
  calc
    (∏ e ∈ A, if e ∈ star v then (-1 : ℝ) else 1) =
        ∏ e ∈ A.filter (fun e => e ∈ star v), (-1 : ℝ) := by
      rw [Finset.prod_filter]
    _ = (-1 : ℝ) ^ (A.filter fun e => e ∈ star v).card := by
      rw [Finset.prod_const]
    _ = (-1 : ℝ) ^ (A ∩ star v).card := by
      rw [Finset.filter_mem_eq_inter]

omit [Fintype E] [Fintype P] [DecidableEq P] in


theorem plaquetteSpin_localGaugeTransform (incidence : P -> Finset E)
    (star : Q -> Finset E) (v : Q) (omega : GaugeConfig E) (p : P) :
    plaquetteSpin incidence (localGaugeTransform star v omega) p =
      (-1 : ℝ) ^ (incidence p ∩ star v).card *
        plaquetteSpin incidence omega p := by
  unfold plaquetteSpin
  simp_rw [gaugeEdgeSpin_localGaugeTransform star v omega]
  rw [Finset.prod_mul_distrib, prod_star_sign]


end LocalGauge
end StatMech.FrontierA

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SpliceST1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.TailSelMPClose.Part2
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000


namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly

open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem sp1_map_uncurry_const {γ α β : Type*} [MeasurableSpace γ] [MeasurableSpace α]
    [MeasurableSpace β] (κ : Measure γ) [IsProbabilityMeasure κ] (ν : Measure α)
    [SigmaFinite ν] {G : γ → α → β} (hG : Measurable (Function.uncurry G)) {ξ : Measure β}
    (hcol : ∀ c, Measure.map (G c) ν = ξ) :
    Measure.map (Function.uncurry G) (κ.prod ν) = ξ := by
  ext T hT
  rw [Measure.map_apply hG hT, Measure.prod_apply (hG hT)]
  have hGc : ∀ c, Measurable (G c) := fun c => hG.comp (measurable_const.prodMk measurable_id)
  have hpt : ∀ c, ν (Prod.mk c ⁻¹' (Function.uncurry G ⁻¹' T)) = ξ T := by
    intro c
    have hset : Prod.mk c ⁻¹' (Function.uncurry G ⁻¹' T) = (G c) ⁻¹' T := by
      ext a; simp [Function.uncurry]
    rw [hset, ← Measure.map_apply (hGc c) hT, hcol c]
  simp_rw [hpt]
  rw [MeasureTheory.lintegral_const, measure_univ, mul_one]


end AdaptDisintegration
end OSSS
end StatMech

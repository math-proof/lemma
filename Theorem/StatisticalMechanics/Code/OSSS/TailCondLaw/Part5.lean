/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailCondLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptCondReduction
import Def.StatisticalMechanics.Code.OSSS.TailCondLaw.Part4
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly

open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem atc_tailCondLawFixed {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hfC : ∀ ω, |f ω| ≤ 1) :
    atc_TailCondLawFixed μ σ f := by
  intro t htn m A
  set e := (σ : Fin n → E) ⟨t, htn⟩ with he
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact atc_tailCondLawFixedDiag μ hpos hμ1 σ hfC e t t m (le_refl t) A
  · exact atc_tailCondLawFixedDiag μ hpos hμ1 σ hfC e t (t+1) m (Nat.le_succ t) A
  · exact atc_tailCondLawFixedCross hpos hμ1 hmono σ hf hfC e t t (t+1) m (le_refl t)
      (Nat.le_succ t) A
  · exact atc_tailCondLawFixedCross hpos hμ1 hmono σ hf hfC e t (t+1) t m (Nat.le_succ t)
      (le_refl t) A

end AdaptDisintegration
end OSSS
end StatMech

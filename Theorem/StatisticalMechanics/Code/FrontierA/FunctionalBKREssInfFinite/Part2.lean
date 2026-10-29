/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKREssInfFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralDual.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralFinite
import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Mathlib.MeasureTheory.Function.EssSup
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKREssInfFinite.Part2
open MeasureTheory
open scoped BigOperators ENNReal NNReal


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem cylinderEssInf_eq_cylinderMin
    (p : E → NNReal) (hp0 : ∀ e, 0 < p e) (hp1 : ∀ e, p e < 1)
    (f : ConfigSpace E → ℝ) (K : Set E) (omega : ConfigSpace E) :
    cylinderEssInf p (fun e => (hp1 e).le) f K omega =
      cylinderMin f K omega := by
  letI : Nonempty (AgreementFiberPoint K omega) :=
    ⟨⟨omega, agreeOn_refl K omega⟩⟩
  have hbdd : BddBelow
      (Set.range fun eta : AgreementFiberPoint K omega => f eta.1) :=
    (Set.toFinite _).bddBelow
  rw [cylinderEssInf, essInf_eq_ciInf
    (agreementFiberMeasure_singleton_ne_zero p hp0 hp1 K omega) hbdd]
  apply le_antisymm
  · obtain ⟨eta, heta, heq⟩ := Finset.exists_mem_eq_inf'
      (agreementFiber_nonempty K omega) f
    calc
      (⨅ a : AgreementFiberPoint K omega, f a.1) ≤
          f (⟨eta, mem_agreementFiber.mp heta⟩ : AgreementFiberPoint K omega).1 :=
        ciInf_le hbdd _
      _ = cylinderMin f K omega := by
        rw [cylinderMin, heq]
  · apply le_ciInf
    intro eta
    exact Finset.inf'_le _ (mem_agreementFiber.mpr eta.2)


end StatMech.FrontierA

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
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKREssInfFinite.Part4
open MeasureTheory
open scoped BigOperators ENNReal NNReal


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


omit [Fintype E] [DecidableEq E] in
theorem bernoulliProductWeight_nonneg
    (p : E → ℝ≥0) (hp : ∀ e, p e ≤ 1) :
    ∀ e b, 0 ≤ bernoulliProductWeight p hp e b :=
  fun _ _ => measureReal_nonneg

omit [Fintype E] [DecidableEq E] in
theorem bernoulliProductWeight_sum
    (p : E → ℝ≥0) (hp : ∀ e, p e ≤ 1) :
    ∀ e, bernoulliProductWeight p hp e false +
      bernoulliProductWeight p hp e true = 1 := by
  intro e
  have hf : (bernoulliMeasure (p e) (hp e)).real {false} =
      ((1 - p e : ℝ≥0) : ℝ) := by
    rw [Measure.real, bernoulliMeasure_apply_false, ENNReal.coe_toReal]
  have ht : (bernoulliMeasure (p e) (hp e)).real {true} = (p e : ℝ) := by
    rw [Measure.real, bernoulliMeasure_apply_true, ENNReal.coe_toReal]
  simp only [bernoulliProductWeight]
  rw [hf, ht, NNReal.coe_sub (hp e), NNReal.coe_one]
  ring


theorem integral_inhomBernoulli_eq_productExpectation
    (p : E → ℝ≥0) (hp : ∀ e, p e ≤ 1) (f : ConfigSpace E → ℝ) :
    ∫ omega, f omega ∂(inhomBernoulliProductMeasure p hp) =
      productExpectation (bernoulliProductWeight p hp) f := by
  rw [integral_fintype Integrable.of_finite]
  unfold productExpectation
  apply Finset.sum_congr rfl
  intro omega _
  rw [inhomBernoulliProductMeasure.real_singleton]
  rfl


theorem integral_prod_inhomBernoulli_eq_dualProductExpectation
    (p : E → ℝ≥0) (hp : ∀ e, p e ≤ 1)
    (F : ConfigSpace E × ConfigSpace E → ℝ) :
    ∫ pair, F pair ∂((inhomBernoulliProductMeasure p hp).prod
      (inhomBernoulliProductMeasure p hp)) =
      dualProductExpectation (bernoulliProductWeight p hp) F := by
  rw [integral_fintype Integrable.of_finite]
  unfold dualProductExpectation
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro omega _
  apply Finset.sum_congr rfl
  intro eta _
  have hsingleton : ({(omega, eta)} : Set
      (ConfigSpace E × ConfigSpace E)) = {omega} ×ˢ {eta} := by
    ext pair
    simp
  rw [hsingleton, Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
  rw [← Measure.real, ← Measure.real,
    inhomBernoulliProductMeasure.real_singleton,
    inhomBernoulliProductMeasure.real_singleton]
  rfl


theorem functionalBKR_essInf_integral
    (p : E → ℝ≥0) (hp0 : ∀ e, 0 < p e) (hp1 : ∀ e, p e < 1)
    (f g : ConfigSpace E → ℝ)
    (hf0 : ∀ omega, 0 ≤ f omega) (hg0 : ∀ omega, 0 ≤ g omega) :
    ∫ omega, functionalDisjointEssMax p (fun e => (hp1 e).le)
        f g omega ∂(inhomBernoulliProductMeasure p (fun e => (hp1 e).le)) ≤
      (∫ omega, f omega
          ∂(inhomBernoulliProductMeasure p (fun e => (hp1 e).le))) *
        ∫ omega, g omega
          ∂(inhomBernoulliProductMeasure p (fun e => (hp1 e).le)) := by
  simp_rw [functionalDisjointEssMax_eq p hp0 hp1]
  rw [integral_inhomBernoulli_eq_productExpectation,
    integral_inhomBernoulli_eq_productExpectation,
    integral_inhomBernoulli_eq_productExpectation]
  exact functionalBKR_real _
    (bernoulliProductWeight_nonneg p (fun e => (hp1 e).le))
    (bernoulliProductWeight_sum p (fun e => (hp1 e).le))
    f g hf0 hg0


theorem dualFunctionalBKR_essInf_integral
    (p : E → ℝ≥0) (hp0 : ∀ e, 0 < p e) (hp1 : ∀ e, p e < 1)
    (f g : ConfigSpace E → ℝ)
    (hf0 : ∀ omega, 0 ≤ f omega) (hg0 : ∀ omega, 0 ≤ g omega) :
    ∫ pair, functionalDisjointEssMaxAt p (fun e => (hp1 e).le)
        f g pair.1 pair.2
      ∂((inhomBernoulliProductMeasure p (fun e => (hp1 e).le)).prod
        (inhomBernoulliProductMeasure p (fun e => (hp1 e).le))) ≤
      ∫ omega, f omega * g omega
        ∂(inhomBernoulliProductMeasure p (fun e => (hp1 e).le)) := by
  simp_rw [functionalDisjointEssMaxAt_eq p hp0 hp1]
  rw [integral_prod_inhomBernoulli_eq_dualProductExpectation,
    integral_inhomBernoulli_eq_productExpectation]
  exact dualFunctionalBKR_real _
    (bernoulliProductWeight_nonneg p (fun e => (hp1 e).le))
    (bernoulliProductWeight_sum p (fun e => (hp1 e).le))
    f g hf0 hg0

end StatMech.FrontierA

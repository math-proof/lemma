import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProduct
open MeasureTheory Set Filter Topology StatMech StatMech.FrontierA


/--
[tendsto_min_natCast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProduct.lean)
-/
@[path]
private lemma tendsto_min_natCast_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {r : ℝ} :
-- imply
  Tendsto (fun n : ℕ => min r n) atTop (𝓝 (r)) := by
-- proof
  apply StatMech.FrontierA.tendsto_min_natCast r

/--
[tendsto_lintegral_of_monotone_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProduct.lean)
-/
@[path]
private lemma tendsto_lintegral_of_monotone_ae_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [MeasurableSpace X]
  {mu : Measure X}
-- given
  (u : ℕ → X → ℝ≥0∞)
  (v : X → ℝ≥0∞)
  (hu : ∀ n, Measurable (u n))
  (hmono : ∀ x, Monotone fun n => u n x)
  (hlim : ∀ᵐ x ∂mu, Tendsto (fun n => u n x) atTop (𝓝 (v x))) :
-- imply
  Tendsto (fun n => ∫⁻ x, u n x ∂mu) atTop (𝓝 (∫⁻ x, v x ∂mu)) := by
-- proof
  apply StatMech.FrontierA.tendsto_lintegral_of_monotone_ae mu u v hu hmono hlim

/--
[measurableFamilyBKR_and_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProduct.lean)
-/
@[path]
private lemma measurableFamilyBKR_and_dual_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (mu e)]
-- given
  (mu : ∀ e, Measure (S e))
  (F G : Set E → (∀ e, S e) → ℝ)
  (hFm : ∀ K, Measurable (F K))
  (hGm : ∀ K, Measurable (G K))
  (hF0 : ∀ K x, 0 ≤ F K x)
  (hG0 : ∀ K x, 0 ≤ G K x)
  (hFdep : ∀ K, PiDependsOn K (F K))
  (hGdep : ∀ K, PiDependsOn K (G K)) :
-- imply
  (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax F G x) ∂Measure.pi mu) ≤ (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F x) ∂Measure.pi mu) * ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax G x) ∂Measure.pi mu ∧ (∫⁻ p, ENNReal.ofReal (piFunctionalFamilyDisjointMaxAt F G p.1 p.2) ∂(Measure.pi mu).prod (Measure.pi mu)) ≤ ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F x * piFunctionalFamilyMax G x) ∂Measure.pi mu := by
-- proof
  apply StatMech.FrontierA.measurableFamilyBKR_and_dual mu F G hFm hGm hF0 hG0 hFdep hGdep

/--
[hasMeasurableFunctionalBKR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProduct.lean)
-/
@[path]
private lemma hasMeasurableFunctionalBKR_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (mu e)]
-- given
  (mu : ∀ e, Measure (S e)) :
-- imply
  HasMeasurableFunctionalBKR mu := by
-- proof
  apply StatMech.FrontierA.hasMeasurableFunctionalBKR mu

/--
[hasMeasurableDualFunctionalBKR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProduct.lean)
-/
@[path]
private lemma hasMeasurableDualFunctionalBKR_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (mu e)]
-- given
  (mu : ∀ e, Measure (S e)) :
-- imply
  HasMeasurableDualFunctionalBKR mu := by
-- proof
  apply StatMech.FrontierA.hasMeasurableDualFunctionalBKR mu

/--
[functionalBKR_generalProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProduct.lean)
-/
@[path]
private lemma functionalBKR_generalProduct_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (mu e)]
-- given
  (mu : ∀ e, Measure (S e))
  (f g : (∀ e, S e) → ℝ)
  (hf : Measurable f)
  (hg : Measurable g)
  (hf0 : ∀ x, 0 ≤ f x)
  (hg0 : ∀ x, 0 ≤ g x) :
-- imply
  (∫⁻ x, ENNReal.ofReal (piFunctionalDisjointEssMax mu f g x) ∂Measure.pi mu) ≤ (∫⁻ x, ENNReal.ofReal (f x) ∂Measure.pi mu) * ∫⁻ x, ENNReal.ofReal (g x) ∂Measure.pi mu := by
-- proof
  apply StatMech.FrontierA.functionalBKR_generalProduct mu f g hf hg hf0 hg0

/--
[dualFunctionalBKR_generalProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProduct.lean)
-/
@[path]
private lemma dualFunctionalBKR_generalProduct_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (mu e)]
-- given
  (mu : ∀ e, Measure (S e))
  (f g : (∀ e, S e) → ℝ)
  (hf : Measurable f)
  (hg : Measurable g)
  (hf0 : ∀ x, 0 ≤ f x)
  (hg0 : ∀ x, 0 ≤ g x) :
-- imply
  (∫⁻ p, ENNReal.ofReal (piFunctionalDisjointEssMaxAt mu f g p.1 p.2) ∂(Measure.pi mu).prod (Measure.pi mu)) ≤ ∫⁻ x, ENNReal.ofReal (f x * g x) ∂Measure.pi mu := by
-- proof
  apply StatMech.FrontierA.dualFunctionalBKR_generalProduct mu f g hf hg hf0 hg0


-- created on 2026-10-23

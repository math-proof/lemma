import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.FunctionalBKREssInfFinite
open MeasureTheory StatMech StatMech.FrontierA


/--
[agreementFiberMeasure_singleton_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKREssInfFinite.lean)
-/
@[path]
private lemma agreementFiberMeasure_singleton_ne_zero_eq
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
  {omega : ConfigSpace E}
  {eta : AgreementFiberPoint K omega}
-- given
  (p : E → ℝ≥0)
  (hp0 : ∀ e, 0 < p e)
  (hp1 : ∀ e, p e < 1) :
-- imply
  agreementFiberMeasure p (fun e => (hp1 e).le) K omega {eta} ≠ 0 := by
-- proof
  apply StatMech.FrontierA.agreementFiberMeasure_singleton_ne_zero p hp0 hp1 K omega eta

/--
[cylinderEssInf_eq_cylinderMin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKREssInfFinite.lean)
-/
@[path]
private lemma cylinderEssInf_eq_cylinderMin_eq
  [Fintype E]
  [DecidableEq E]
  {f : ConfigSpace E → ℝ}
  {K : Set E}
  {omega : ConfigSpace E}
-- given
  (p : E → ℝ≥0)
  (hp0 : ∀ e, 0 < p e)
  (hp1 : ∀ e, p e < 1) :
-- imply
  cylinderEssInf p (fun e => (hp1 e).le) f K omega = cylinderMin f K omega := by
-- proof
  apply StatMech.FrontierA.cylinderEssInf_eq_cylinderMin p hp0 hp1 f K omega

/--
[functionalDisjointEssMaxAt_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKREssInfFinite.lean)
-/
@[path]
private lemma functionalDisjointEssMaxAt_eq_eq
  [Fintype E]
  [DecidableEq E]
  {f g : ConfigSpace E → ℝ}
  {omega eta : ConfigSpace E}
-- given
  (p : E → ℝ≥0)
  (hp0 : ∀ e, 0 < p e)
  (hp1 : ∀ e, p e < 1) :
-- imply
  functionalDisjointEssMaxAt p (fun e => (hp1 e).le) f g omega eta = functionalDisjointMaxAt f g omega eta := by
-- proof
  apply StatMech.FrontierA.functionalDisjointEssMaxAt_eq p hp0 hp1 f g omega eta

/--
[functionalDisjointEssMax_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKREssInfFinite.lean)
-/
@[path]
private lemma functionalDisjointEssMax_eq_eq
  [Fintype E]
  [DecidableEq E]
  {f g : ConfigSpace E → ℝ}
  {omega : ConfigSpace E}
-- given
  (p : E → ℝ≥0)
  (hp0 : ∀ e, 0 < p e)
  (hp1 : ∀ e, p e < 1) :
-- imply
  functionalDisjointEssMax p (fun e => (hp1 e).le) f g omega = functionalDisjointMax f g omega := by
-- proof
  apply StatMech.FrontierA.functionalDisjointEssMax_eq p hp0 hp1 f g omega

/--
[bernoulliProductWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKREssInfFinite.lean)
-/
@[path]
private lemma bernoulliProductWeight_nonneg_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (p : E → ℝ≥0)
  (hp : ∀ e, p e ≤ 1) :
-- imply
  ∀ e b, 0 ≤ bernoulliProductWeight p hp e b := by
-- proof
  apply StatMech.FrontierA.bernoulliProductWeight_nonneg p hp

/--
[bernoulliProductWeight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKREssInfFinite.lean)
-/
@[path]
private lemma bernoulliProductWeight_sum_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (p : E → ℝ≥0)
  (hp : ∀ e, p e ≤ 1) :
-- imply
  ∀ e, bernoulliProductWeight p hp e false + bernoulliProductWeight p hp e true = 1 := by
-- proof
  apply StatMech.FrontierA.bernoulliProductWeight_sum p hp

/--
[integral_inhomBernoulli_eq_productExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKREssInfFinite.lean)
-/
@[path]
private lemma integral_inhomBernoulli_eq_productExpectation_eq
  [Fintype E]
  [DecidableEq E]
  {f : ConfigSpace E → ℝ}
-- given
  (p : E → ℝ≥0)
  (hp : ∀ e, p e ≤ 1) :
-- imply
  ∫ omega, f omega ∂(inhomBernoulliProductMeasure p hp) = productExpectation (bernoulliProductWeight p hp) f := by
-- proof
  apply StatMech.FrontierA.integral_inhomBernoulli_eq_productExpectation p hp f

/--
[integral_prod_inhomBernoulli_eq_dualProductExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKREssInfFinite.lean)
-/
@[path]
private lemma integral_prod_inhomBernoulli_eq_dualProductExpectation_eq
  [Fintype E]
  [DecidableEq E]
  {F : ConfigSpace E × ConfigSpace E → ℝ}
-- given
  (p : E → ℝ≥0)
  (hp : ∀ e, p e ≤ 1) :
-- imply
  ∫ pair, F pair ∂((inhomBernoulliProductMeasure p hp).prod (inhomBernoulliProductMeasure p hp)) = dualProductExpectation (bernoulliProductWeight p hp) F := by
-- proof
  apply StatMech.FrontierA.integral_prod_inhomBernoulli_eq_dualProductExpectation p hp F

/--
[functionalBKR_essInf_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKREssInfFinite.lean)
-/
@[path]
private lemma functionalBKR_essInf_integral_eq
  [Fintype E]
  [DecidableEq E]
  {f g : ConfigSpace E → ℝ}
-- given
  (p : E → ℝ≥0)
  (hp0 : ∀ e, 0 < p e)
  (hp1 : ∀ e, p e < 1)
  (hf0 : ∀ omega, 0 ≤ f omega)
  (hg0 : ∀ omega, 0 ≤ g omega) :
-- imply
  ∫ omega, functionalDisjointEssMax p (fun e => (hp1 e).le) f g omega ∂(inhomBernoulliProductMeasure p (fun e => (hp1 e).le)) ≤ (∫ omega, f omega ∂(inhomBernoulliProductMeasure p (fun e => (hp1 e).le))) * ∫ omega, g omega ∂(inhomBernoulliProductMeasure p (fun e => (hp1 e).le)) := by
-- proof
  apply StatMech.FrontierA.functionalBKR_essInf_integral p hp0 hp1 f g hf0 hg0

/--
[dualFunctionalBKR_essInf_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKREssInfFinite.lean)
-/
@[path]
private lemma dualFunctionalBKR_essInf_integral_eq
  [Fintype E]
  [DecidableEq E]
  {f g : ConfigSpace E → ℝ}
-- given
  (p : E → ℝ≥0)
  (hp0 : ∀ e, 0 < p e)
  (hp1 : ∀ e, p e < 1)
  (hf0 : ∀ omega, 0 ≤ f omega)
  (hg0 : ∀ omega, 0 ≤ g omega) :
-- imply
  ∫ pair, functionalDisjointEssMaxAt p (fun e => (hp1 e).le) f g pair.1 pair.2 ∂((inhomBernoulliProductMeasure p (fun e => (hp1 e).le)).prod (inhomBernoulliProductMeasure p (fun e => (hp1 e).le))) ≤ ∫ omega, f omega * g omega ∂(inhomBernoulliProductMeasure p (fun e => (hp1 e).le)) := by
-- proof
  apply StatMech.FrontierA.dualFunctionalBKR_essInf_integral p hp0 hp1 f g hf0 hg0


-- created on 2026-10-23

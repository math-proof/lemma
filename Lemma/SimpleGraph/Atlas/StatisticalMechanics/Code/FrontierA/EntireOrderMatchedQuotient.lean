import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.EntireOrderMatchedQuotient
open Set StatMech StatMech.FrontierA


/--
[entireOrderMatchedQuotient_meromorphicNFOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/EntireOrderMatchedQuotient.lean)
-/
@[path]
private lemma entireOrderMatchedQuotient_meromorphicNFOn_eq
  {f g : ℂ → ℂ} :
-- imply
  MeromorphicNFOn (entireOrderMatchedQuotient f g) Set.univ := by
-- proof
  apply StatMech.FrontierA.entireOrderMatchedQuotient_meromorphicNFOn f g

/--
[entireOrderMatchedQuotient_order_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/EntireOrderMatchedQuotient.lean)
-/
@[path]
private lemma entireOrderMatchedQuotient_order_eq_zero_eq
  {f g : ℂ → ℂ}
  {z : ℂ}
-- given
  (hf : ∀ z, AnalyticAt ℂ f z)
  (hg : ∀ z, AnalyticAt ℂ g z)
  (horder : ∀ z, analyticOrderAt f z = analyticOrderAt g z)
  (hfinite : ∀ z, analyticOrderAt g z ≠ ⊤) :
-- imply
  meromorphicOrderAt (entireOrderMatchedQuotient f g) z = 0 := by
-- proof
  apply StatMech.FrontierA.entireOrderMatchedQuotient_order_eq_zero hf hg horder hfinite z

/--
[analyticAt_entireOrderMatchedQuotient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/EntireOrderMatchedQuotient.lean)
-/
@[path]
private lemma analyticAt_entireOrderMatchedQuotient_eq
  {f g : ℂ → ℂ}
  {z : ℂ}
-- given
  (hf : ∀ z, AnalyticAt ℂ f z)
  (hg : ∀ z, AnalyticAt ℂ g z)
  (horder : ∀ z, analyticOrderAt f z = analyticOrderAt g z)
  (hfinite : ∀ z, analyticOrderAt g z ≠ ⊤) :
-- imply
  AnalyticAt ℂ (entireOrderMatchedQuotient f g) z := by
-- proof
  apply StatMech.FrontierA.analyticAt_entireOrderMatchedQuotient hf hg horder hfinite z

/--
[entireOrderMatchedQuotient_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/EntireOrderMatchedQuotient.lean)
-/
@[path]
private lemma entireOrderMatchedQuotient_ne_zero_eq
  {f g : ℂ → ℂ}
  {z : ℂ}
-- given
  (hf : ∀ z, AnalyticAt ℂ f z)
  (hg : ∀ z, AnalyticAt ℂ g z)
  (horder : ∀ z, analyticOrderAt f z = analyticOrderAt g z)
  (hfinite : ∀ z, analyticOrderAt g z ≠ ⊤) :
-- imply
  entireOrderMatchedQuotient f g z ≠ 0 := by
-- proof
  apply StatMech.FrontierA.entireOrderMatchedQuotient_ne_zero hf hg horder hfinite z

/--
[entireOrderMatchedQuotient_mul_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/EntireOrderMatchedQuotient.lean)
-/
@[path]
private lemma entireOrderMatchedQuotient_mul_eq_eq
  {f g : ℂ → ℂ}
  {z : ℂ}
-- given
  (hf : ∀ z, AnalyticAt ℂ f z)
  (hg : ∀ z, AnalyticAt ℂ g z)
  (horder : ∀ z, analyticOrderAt f z = analyticOrderAt g z) :
-- imply
  entireOrderMatchedQuotient f g z * g z = f z := by
-- proof
  apply StatMech.FrontierA.entireOrderMatchedQuotient_mul_eq hf hg horder z

/--
[exists_entire_zeroFree_quotient_of_analyticOrderAt_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/EntireOrderMatchedQuotient.lean)
-/
@[path]
private lemma exists_entire_zeroFree_quotient_of_analyticOrderAt_eq_eq
  {f g : ℂ → ℂ}
-- given
  (hf : ∀ z, AnalyticAt ℂ f z)
  (hg : ∀ z, AnalyticAt ℂ g z)
  (horder : ∀ z, analyticOrderAt f z = analyticOrderAt g z)
  (hfinite : ∀ z, analyticOrderAt g z ≠ ⊤) :
-- imply
  ∃ Q : ℂ → ℂ, (∀ z, AnalyticAt ℂ Q z) ∧ (∀ z, Q z ≠ 0) ∧ f = fun z => Q z * g z := by
-- proof
  apply StatMech.FrontierA.exists_entire_zeroFree_quotient_of_analyticOrderAt_eq hf hg horder hfinite


-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Analysis.Fourier.FourierLaplace
open MeasureTheory


namespace FourierTest

/--
[compactlySupportedExample_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Fourier/FourierLaplace.lean)
-/
@[path]
private lemma compactlySupportedExample_integrable : Integrable compactlySupportedExample := by
  exact IntegrableOn.integrable_indicator
    (integrableOn_const measure_Icc_lt_top.ne) measurableSet_Icc

end FourierTest

namespace FourierTest

/--
[compactlySupportedExample_hasCompactSupport](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Fourier/FourierLaplace.lean)
-/
@[path]
private lemma compactlySupportedExample_hasCompactSupport :
  HasCompactSupport compactlySupportedExample := by
  apply HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc
  intro x hx
  rw [compactlySupportedExample, Set.indicator_apply, ite_eq_right hx]

end FourierTest


-- created on 2026-10-23

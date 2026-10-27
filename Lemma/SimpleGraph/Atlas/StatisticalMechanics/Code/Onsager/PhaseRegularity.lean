import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part12
open StatMech StatMech.Onsager


/--
[ons_hasDerivAt_gInt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_hasDerivAt_gInt_eq
  {beta k1 k2 : ℝ} :
-- imply
  HasDerivAt (fun b => ons_gInt b k1 k2) (ons_gIntBetaDeriv beta k1 k2) beta := by
-- proof
  apply StatMech.Onsager.ons_hasDerivAt_gInt beta k1 k2

/--
[ons_hasDerivAt_gIntBetaDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_hasDerivAt_gIntBetaDeriv_eq
  {beta k1 k2 : ℝ} :
-- imply
  HasDerivAt (fun b => ons_gIntBetaDeriv b k1 k2) (ons_gIntBetaDeriv2 beta k1 k2) beta := by
-- proof
  apply StatMech.Onsager.ons_hasDerivAt_gIntBetaDeriv beta k1 k2

/--
[ons_hasDerivAt_log_gInt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_hasDerivAt_log_gInt_eq
  {beta k1 k2 : ℝ}
-- given
  (hne : ons_gInt beta k1 k2 ≠ 0) :
-- imply
  HasDerivAt (fun b => Real.log (ons_gInt b k1 k2)) (ons_logGIntBetaDeriv beta k1 k2) beta := by
-- proof
  apply StatMech.Onsager.ons_hasDerivAt_log_gInt beta k1 k2 hne

/--
[ons_hasDerivAt_logGIntBetaDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_hasDerivAt_logGIntBetaDeriv_eq
  {beta k1 k2 : ℝ}
-- given
  (hne : ons_gInt beta k1 k2 ≠ 0) :
-- imply
  HasDerivAt (fun b => ons_logGIntBetaDeriv b k1 k2) (ons_logGIntBetaDeriv2 beta k1 k2) beta := by
-- proof
  apply StatMech.Onsager.ons_hasDerivAt_logGIntBetaDeriv beta k1 k2 hne

/--
[ons_cosh_betaC_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_cosh_betaC_sq_eq :
-- imply
  Real.cosh (2 * ons_betaC) ^ 2 = 2 := by
-- proof
  apply StatMech.Onsager.ons_cosh_betaC_sq

/--
[ons_gIntBetaDeriv_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_gIntBetaDeriv_betaC_eq
  {k1 k2 : ℝ} :
-- imply
  ons_gIntBetaDeriv ons_betaC k1 k2 = 2 * Real.cosh (2 * ons_betaC) * (2 - Real.cos k1 - Real.cos k2) := by
-- proof
  apply StatMech.Onsager.ons_gIntBetaDeriv_betaC k1 k2

/--
[ons_gIntBetaDeriv2_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_gIntBetaDeriv2_betaC_eq
  {k1 k2 : ℝ} :
-- imply
  ons_gIntBetaDeriv2 ons_betaC k1 k2 = 4 * (2 - Real.cos k1 - Real.cos k2) + 16 := by
-- proof
  apply StatMech.Onsager.ons_gIntBetaDeriv2_betaC k1 k2

/--
[ons_logGIntBetaDeriv_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_logGIntBetaDeriv_betaC_eq
  {k1 k2 : ℝ}
-- given
  (hne : 2 - Real.cos k1 - Real.cos k2 ≠ 0) :
-- imply
  ons_logGIntBetaDeriv ons_betaC k1 k2 = 2 * Real.cosh (2 * ons_betaC) := by
-- proof
  apply StatMech.Onsager.ons_logGIntBetaDeriv_betaC k1 k2 hne

/--
[ons_logGIntBetaDeriv2_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_logGIntBetaDeriv2_betaC_eq
  {k1 k2 : ℝ}
-- given
  (hne : 2 - Real.cos k1 - Real.cos k2 ≠ 0) :
-- imply
  ons_logGIntBetaDeriv2 ons_betaC k1 k2 = -4 + 16 / (2 - Real.cos k1 - Real.cos k2) := by
-- proof
  apply StatMech.Onsager.ons_logGIntBetaDeriv2_betaC k1 k2 hne

/--
[ons_criticalDenom_le_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalDenom_le_sq_eq
  {x y : ℝ} :
-- imply
  2 - Real.cos x - Real.cos y ≤ (x ^ 2 + y ^ 2) / 2 := by
-- proof
  apply StatMech.Onsager.ons_criticalDenom_le_sq x y

/--
[ons_criticalDenom_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalDenom_pos_eq
  {x y : ℝ}
-- given
  (hx : 0 < x)
  (hxpi : x ≤ Real.pi) :
-- imply
  0 < 2 - Real.cos x - Real.cos y := by
-- proof
  apply StatMech.Onsager.ons_criticalDenom_pos hx hxpi

/--
[ons_criticalKernel_lower_on_wedge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalKernel_lower_on_wedge_eq
  {x y : ℝ}
-- given
  (hx : 0 < x)
  (h2xpi : 2 * x ≤ Real.pi)
  (hxy : x ≤ y)
  (hy2x : y ≤ 2 * x) :
-- imply
  2 / (5 * x ^ 2) ≤ 1 / (2 - Real.cos x - Real.cos y) := by
-- proof
  apply StatMech.Onsager.ons_criticalKernel_lower_on_wedge hx h2xpi hxy hy2x

/--
[ons_criticalKernel_innerIntegral_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalKernel_innerIntegral_lower_eq
  {x : ℝ}
-- given
  (hx : 0 < x)
  (h2xpi : 2 * x ≤ Real.pi) :
-- imply
  2 / (5 * x) ≤ ∫ y in x..(2 * x), 1 / (2 - Real.cos x - Real.cos y) := by
-- proof
  apply StatMech.Onsager.ons_criticalKernel_innerIntegral_lower hx h2xpi

/--
[ons_logKernel_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_logKernel_integral_eq
  {epsilon delta : ℝ}
-- given
  (hepsilon : 0 < epsilon)
  (hed : epsilon ≤ delta) :
-- imply
  (∫ x in epsilon..delta, 2 / (5 * x)) = (2 / 5 : ℝ) * Real.log (delta / epsilon) := by
-- proof
  apply StatMech.Onsager.ons_logKernel_integral hepsilon hed

/--
[ons_logKernel_cutoff_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_logKernel_cutoff_tendsto_eq
  {delta : ℝ}
-- given
  (hdelta : 0 < delta) :
-- imply
  Filter.Tendsto (fun n : ℕ => (2 / 5 : ℝ) * Real.log (delta / Real.exp (-(n : ℝ)))) Filter.atTop Filter.atTop := by
-- proof
  apply StatMech.Onsager.ons_logKernel_cutoff_tendsto delta hdelta

/--
[ons_one_sub_cos_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_one_sub_cos_pos_eq
  {epsilon : ℝ}
-- given
  (hepsilon : 0 < epsilon)
  (hepsilonPi : epsilon ≤ Real.pi) :
-- imply
  0 < 1 - Real.cos epsilon := by
-- proof
  apply StatMech.Onsager.ons_one_sub_cos_pos hepsilon hepsilonPi

/--
[ons_criticalKernelClamp_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalKernelClamp_continuous_eq
  {epsilon : ℝ}
-- given
  (hcut : 0 < 1 - Real.cos epsilon) :
-- imply
  Continuous (Function.uncurry (ons_criticalKernelClamp epsilon)) := by
-- proof
  apply StatMech.Onsager.ons_criticalKernelClamp_continuous epsilon hcut

/--
[ons_criticalKernelClamp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalKernelClamp_eq_eq
  {epsilon delta x y : ℝ}
-- given
  (hepsilon : 0 ≤ epsilon)
  (hdeltaPi : delta ≤ Real.pi)
  (hx : x ∈ Set.Icc epsilon delta) :
-- imply
  ons_criticalKernelClamp epsilon x y = 1 / (2 - Real.cos x - Real.cos y) := by
-- proof
  apply StatMech.Onsager.ons_criticalKernelClamp_eq hepsilon hdeltaPi hx

/--
[ons_wedgeIntegral_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_wedgeIntegral_continuous_eq
  {F : ℝ → ℝ → ℝ}
-- given
  (hjoint : Continuous (Function.uncurry F)) :
-- imply
  Continuous (fun x : ℝ => ∫ y in x..(2 * x), F x y) := by
-- proof
  apply StatMech.Onsager.ons_wedgeIntegral_continuous hjoint

/--
[ons_criticalKernelClamp_inner_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalKernelClamp_inner_continuous_eq
  {epsilon : ℝ}
-- given
  (hcut : 0 < 1 - Real.cos epsilon) :
-- imply
  Continuous (fun x : ℝ => ∫ y in x..(2 * x), ons_criticalKernelClamp epsilon x y) := by
-- proof
  apply StatMech.Onsager.ons_criticalKernelClamp_inner_continuous epsilon hcut

/--
[ons_criticalKernel_inner_continuousOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalKernel_inner_continuousOn_eq
  {epsilon delta : ℝ}
-- given
  (hepsilon : 0 < epsilon)
  (hed : epsilon ≤ delta)
  (hdeltaPi : delta ≤ Real.pi) :
-- imply
  ContinuousOn (fun x : ℝ => ∫ y in x..(2 * x), 1 / (2 - Real.cos x - Real.cos y)) (Set.Icc epsilon delta) := by
-- proof
  apply StatMech.Onsager.ons_criticalKernel_inner_continuousOn hepsilon hed hdeltaPi

/--
[ons_criticalKernel_wedgeIntegral_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalKernel_wedgeIntegral_lower_eq
  {epsilon delta : ℝ}
-- given
  (hepsilon : 0 < epsilon)
  (hed : epsilon ≤ delta)
  (h2deltaPi : 2 * delta ≤ Real.pi) :
-- imply
  (2 / 5 : ℝ) * Real.log (delta / epsilon) ≤ ∫ x in epsilon..delta, ∫ y in x..(2 * x), 1 / (2 - Real.cos x - Real.cos y) := by
-- proof
  apply StatMech.Onsager.ons_criticalKernel_wedgeIntegral_lower hepsilon hed h2deltaPi

/--
[ons_criticalKernel_wedgeCutoff_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalKernel_wedgeCutoff_tendsto_eq :
-- imply
  Filter.Tendsto (fun n : ℕ => ∫ x in Real.exp (-(n : ℝ))..1, ∫ y in x..(2 * x), 1 / (2 - Real.cos x - Real.cos y)) Filter.atTop Filter.atTop := by
-- proof
  apply StatMech.Onsager.ons_criticalKernel_wedgeCutoff_tendsto

/--
[ons_criticalSecondKernel_lower_on_wedge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalSecondKernel_lower_on_wedge_eq
  {x y : ℝ}
-- given
  (hx : 0 < x)
  (h2xpi : 2 * x ≤ Real.pi)
  (hxy : x ≤ y)
  (hy2x : y ≤ 2 * x) :
-- imply
  -4 + 32 / (5 * x ^ 2) ≤ ons_logGIntBetaDeriv2 ons_betaC x y := by
-- proof
  apply StatMech.Onsager.ons_criticalSecondKernel_lower_on_wedge hx h2xpi hxy hy2x

/--
[ons_criticalSecondKernel_innerIntegral_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalSecondKernel_innerIntegral_lower_eq
  {x : ℝ}
-- given
  (hx : 0 < x)
  (h2xpi : 2 * x ≤ Real.pi) :
-- imply
  -4 * x + 32 / (5 * x) ≤ ∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y := by
-- proof
  apply StatMech.Onsager.ons_criticalSecondKernel_innerIntegral_lower hx h2xpi

/--
[ons_criticalSecondKernelClamp_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalSecondKernelClamp_continuous_eq
  {epsilon : ℝ}
-- given
  (hcut : 0 < 1 - Real.cos epsilon) :
-- imply
  Continuous (Function.uncurry (ons_criticalSecondKernelClamp epsilon)) := by
-- proof
  apply StatMech.Onsager.ons_criticalSecondKernelClamp_continuous epsilon hcut

/--
[ons_criticalSecondKernel_inner_continuousOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalSecondKernel_inner_continuousOn_eq
  {epsilon delta : ℝ}
-- given
  (hepsilon : 0 < epsilon)
  (hed : epsilon ≤ delta)
  (hdeltaPi : delta ≤ Real.pi) :
-- imply
  ContinuousOn (fun x : ℝ => ∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y) (Set.Icc epsilon delta) := by
-- proof
  apply StatMech.Onsager.ons_criticalSecondKernel_inner_continuousOn hepsilon hed hdeltaPi

/--
[ons_criticalSecondComparison_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalSecondComparison_integral_eq
  {epsilon : ℝ}
-- given
  (hepsilon : 0 < epsilon)
  (hepsilonOne : epsilon ≤ 1) :
-- imply
  (∫ x in epsilon..1, (-4 + 32 / (5 * x))) = -4 * (1 - epsilon) + (32 / 5 : ℝ) * Real.log (1 / epsilon) := by
-- proof
  apply StatMech.Onsager.ons_criticalSecondComparison_integral hepsilon hepsilonOne

/--
[ons_criticalSecond_wedgeCutoff_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalSecond_wedgeCutoff_lower_eq
  {n : ℕ} :
-- imply
  -4 + (32 / 5 : ℝ) * (n : ℝ) ≤ ∫ x in Real.exp (-(n : ℝ))..1, ∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y := by
-- proof
  apply StatMech.Onsager.ons_criticalSecond_wedgeCutoff_lower n

/--
[ons_criticalSecond_wedgeCutoff_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalSecond_wedgeCutoff_tendsto_eq :
-- imply
  Filter.Tendsto (fun n : ℕ => ∫ x in Real.exp (-(n : ℝ))..1, ∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y) Filter.atTop Filter.atTop := by
-- proof
  apply StatMech.Onsager.ons_criticalSecond_wedgeCutoff_tendsto

/--
[ons_criticalSecondKernel_ge_neg_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalSecondKernel_ge_neg_four_eq
  {x y : ℝ}
-- given
  (hx : 0 < x)
  (hxpi : x ≤ Real.pi) :
-- imply
  -4 ≤ ons_logGIntBetaDeriv2 ons_betaC x y := by
-- proof
  apply StatMech.Onsager.ons_criticalSecondKernel_ge_neg_four hx hxpi

/--
[ons_criticalSecondKernel_intervalIntegrable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalSecondKernel_intervalIntegrable_eq
  {x a b : ℝ}
-- given
  (hx : 0 < x)
  (hxpi : x ≤ Real.pi) :
-- imply
  IntervalIntegrable (fun y : ℝ => ons_logGIntBetaDeriv2 ons_betaC x y) MeasureTheory.volume a b := by
-- proof
  apply StatMech.Onsager.ons_criticalSecondKernel_intervalIntegrable hx hxpi

/--
[ons_criticalSecondKernel_interval_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalSecondKernel_interval_lower_eq
  {x a b : ℝ}
-- given
  (hx : 0 < x)
  (hxpi : x ≤ Real.pi)
  (hab : a ≤ b) :
-- imply
  -4 * (b - a) ≤ ∫ y in a..b, ons_logGIntBetaDeriv2 ons_betaC x y := by
-- proof
  apply StatMech.Onsager.ons_criticalSecondKernel_interval_lower hx hxpi hab

/--
[ons_criticalSecondKernel_rectInner_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalSecondKernel_rectInner_lower_eq
  {x : ℝ}
-- given
  (hx : 0 < x)
  (hxone : x ≤ 1) :
-- imply
  (∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y) - 8 ≤ ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y := by
-- proof
  apply StatMech.Onsager.ons_criticalSecondKernel_rectInner_lower hx hxone

/--
[ons_criticalSecond_rectInner_continuousOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalSecond_rectInner_continuousOn_eq
  {epsilon delta : ℝ}
-- given
  (hepsilon : 0 < epsilon)
  (hed : epsilon ≤ delta)
  (hdeltaPi : delta ≤ Real.pi) :
-- imply
  ContinuousOn (fun x : ℝ => ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y) (Set.Icc epsilon delta) := by
-- proof
  apply StatMech.Onsager.ons_criticalSecond_rectInner_continuousOn hepsilon hed hdeltaPi

/--
[ons_criticalSecond_fixedInner_continuousOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalSecond_fixedInner_continuousOn_eq
  {epsilon delta a b : ℝ}
-- given
  (hepsilon : 0 < epsilon)
  (hed : epsilon ≤ delta)
  (hdeltaPi : delta ≤ Real.pi) :
-- imply
  ContinuousOn (fun x : ℝ => ∫ y in a..b, ons_logGIntBetaDeriv2 ons_betaC x y) (Set.Icc epsilon delta) := by
-- proof
  apply StatMech.Onsager.ons_criticalSecond_fixedInner_continuousOn hepsilon hed hdeltaPi

/--
[ons_criticalSecond_rectCutoff_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalSecond_rectCutoff_lower_eq
  {n : ℕ} :
-- imply
  -12 + (32 / 5 : ℝ) * (n : ℝ) ≤ ∫ x in Real.exp (-(n : ℝ))..1, ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y := by
-- proof
  apply StatMech.Onsager.ons_criticalSecond_rectCutoff_lower n

/--
[ons_criticalSecond_rectCutoff_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalSecond_rectCutoff_tendsto_eq :
-- imply
  Filter.Tendsto (fun n : ℕ => ∫ x in Real.exp (-(n : ℝ))..1, ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y) Filter.atTop Filter.atTop := by
-- proof
  apply StatMech.Onsager.ons_criticalSecond_rectCutoff_tendsto

/--
[ons_criticalSecond_positiveInner_rect_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalSecond_positiveInner_rect_lower_eq
  {x : ℝ}
-- given
  (hx : 0 < x)
  (hxone : x ≤ 1) :
-- imply
  (∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y) - 4 * Real.pi ≤ ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y := by
-- proof
  apply StatMech.Onsager.ons_criticalSecond_positiveInner_rect_lower hx hxone

/--
[ons_criticalSecond_positiveQuadrantCutoff_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalSecond_positiveQuadrantCutoff_lower_eq
  {n : ℕ} :
-- imply
  -12 - 4 * Real.pi ^ 2 + (32 / 5 : ℝ) * (n : ℝ) ≤ ∫ x in Real.exp (-(n : ℝ))..Real.pi, ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y := by
-- proof
  apply StatMech.Onsager.ons_criticalSecond_positiveQuadrantCutoff_lower n

/--
[ons_criticalSecond_positiveQuadrantCutoff_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalSecond_positiveQuadrantCutoff_tendsto_eq :
-- imply
  Filter.Tendsto (fun n : ℕ => ∫ x in Real.exp (-(n : ℝ))..Real.pi, ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y) Filter.atTop Filter.atTop := by
-- proof
  apply StatMech.Onsager.ons_criticalSecond_positiveQuadrantCutoff_tendsto

/--
[ons_logGIntBetaDeriv2_neg_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_logGIntBetaDeriv2_neg_left_eq
  {beta x y : ℝ} :
-- imply
  ons_logGIntBetaDeriv2 beta (-x) y = ons_logGIntBetaDeriv2 beta x y := by
-- proof
  apply StatMech.Onsager.ons_logGIntBetaDeriv2_neg_left beta x y

/--
[ons_logGIntBetaDeriv2_neg_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_logGIntBetaDeriv2_neg_right_eq
  {beta x y : ℝ} :
-- imply
  ons_logGIntBetaDeriv2 beta x (-y) = ons_logGIntBetaDeriv2 beta x y := by
-- proof
  apply StatMech.Onsager.ons_logGIntBetaDeriv2_neg_right beta x y

/--
[ons_criticalSecond_inner_full_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalSecond_inner_full_eq_two_eq
  {x : ℝ}
-- given
  (hx : 0 < x)
  (hxpi : x ≤ Real.pi) :
-- imply
  (∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y) = 2 * ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y := by
-- proof
  apply StatMech.Onsager.ons_criticalSecond_inner_full_eq_two hx hxpi

/--
[ons_criticalSecond_fullCutoff_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalSecond_fullCutoff_eq_four_eq
  {n : ℕ} :
-- imply
  ((∫ x in (-Real.pi)..(-Real.exp (-(n : ℝ))), ∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y) + ∫ x in Real.exp (-(n : ℝ))..Real.pi, ∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y) = 4 * ∫ x in Real.exp (-(n : ℝ))..Real.pi, ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y := by
-- proof
  apply StatMech.Onsager.ons_criticalSecond_fullCutoff_eq_four n

/--
[ons_criticalSecond_fullCutoff_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalSecond_fullCutoff_tendsto_eq :
-- imply
  Filter.Tendsto (fun n : ℕ => (∫ x in (-Real.pi)..(-Real.exp (-(n : ℝ))), ∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y) + ∫ x in Real.exp (-(n : ℝ))..Real.pi, ∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y) Filter.atTop Filter.atTop := by
-- proof
  apply StatMech.Onsager.ons_criticalSecond_fullCutoff_tendsto

/--
[ons_cos_lt_one_of_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_cos_lt_one_of_mem_Icc_eq
  {x : ℝ}
-- given
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hne : x ≠ 0) :
-- imply
  Real.cos x < 1 := by
-- proof
  apply StatMech.Onsager.ons_cos_lt_one_of_mem_Icc hx hne

/--
[ons_criticalDenom_pos_of_mem_Icc_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalDenom_pos_of_mem_Icc_left_eq
  {x y : ℝ}
-- given
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hne : x ≠ 0) :
-- imply
  0 < 2 - Real.cos x - Real.cos y := by
-- proof
  apply StatMech.Onsager.ons_criticalDenom_pos_of_mem_Icc_left hx hne

/--
[ons_criticalFirst_inner_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalFirst_inner_integral_eq
  {x : ℝ}
-- given
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  (∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv ons_betaC x y) = (2 * Real.pi) * (2 * Real.cosh (2 * ons_betaC)) := by
-- proof
  apply StatMech.Onsager.ons_criticalFirst_inner_integral x hx

/--
[ons_criticalFirst_double_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalFirst_double_integral_eq :
-- imply
  (∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv ons_betaC x y) = 8 * Real.pi ^ 2 * Real.cosh (2 * ons_betaC) := by
-- proof
  apply StatMech.Onsager.ons_criticalFirst_double_integral

/--
[ons_criticalFirst_normalized_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalFirst_normalized_integral_eq :
-- imply
  (1 / (8 * Real.pi ^ 2)) * (∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv ons_betaC x y) = Real.cosh (2 * ons_betaC) := by
-- proof
  apply StatMech.Onsager.ons_criticalFirst_normalized_integral

/--
[ons_cosh_betaC_eq_sqrt_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_cosh_betaC_eq_sqrt_two_eq :
-- imply
  Real.cosh (2 * ons_betaC) = Real.sqrt 2 := by
-- proof
  apply StatMech.Onsager.ons_cosh_betaC_eq_sqrt_two

/--
[ons_criticalFirst_normalized_integral_eq_sqrt_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalFirst_normalized_integral_eq_sqrt_two_eq :
-- imply
  (1 / (8 * Real.pi ^ 2)) * (∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv ons_betaC x y) = Real.sqrt 2 := by
-- proof
  apply StatMech.Onsager.ons_criticalFirst_normalized_integral_eq_sqrt_two

/--
[ons_noncriticalGap_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_noncriticalGap_pos_eq
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC) :
-- imply
  0 < ons_noncriticalGap beta := by
-- proof
  apply StatMech.Onsager.ons_noncriticalGap_pos hbeta hcrit

/--
[ons_noncriticalNeighborhood_mem_nhds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_noncriticalNeighborhood_mem_nhds_eq
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC) :
-- imply
  ons_noncriticalNeighborhood beta ∈ nhds beta := by
-- proof
  apply StatMech.Onsager.ons_noncriticalNeighborhood_mem_nhds hbeta hcrit

/--
[ons_gInt_uniform_lower_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_gInt_uniform_lower_noncritical_eq
  {beta b k1 k2 : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC)
  (hb : b ∈ ons_noncriticalNeighborhood beta) :
-- imply
  (ons_noncriticalGap beta / 2) ^ 2 ≤ ons_gInt b k1 k2 := by
-- proof
  apply StatMech.Onsager.ons_gInt_uniform_lower_noncritical hbeta hcrit hb

/--
[ons_gInt_pos_noncriticalNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_gInt_pos_noncriticalNeighborhood_eq
  {beta b k1 k2 : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC)
  (hb : b ∈ ons_noncriticalNeighborhood beta) :
-- imply
  0 < ons_gInt b k1 k2 := by
-- proof
  apply StatMech.Onsager.ons_gInt_pos_noncriticalNeighborhood hbeta hcrit hb

/--
[ons_logGIntBetaDeriv_abs_le_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_logGIntBetaDeriv_abs_le_noncritical_eq
  {beta b k1 k2 : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC)
  (hb : b ∈ ons_noncriticalNeighborhood beta) :
-- imply
  |ons_logGIntBetaDeriv b k1 k2| ≤ (2 * (|Real.cosh (2 * beta)| + 1) * (2 * (|Real.sinh (2 * beta)| + 1) + 2)) / (ons_noncriticalGap beta / 2) ^ 2 := by
-- proof
  apply StatMech.Onsager.ons_logGIntBetaDeriv_abs_le_noncritical hbeta hcrit hb

/--
[ons_log_gInt_continuous_momenta_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_log_gInt_continuous_momenta_noncritical_eq
  {beta b : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC)
  (hb : b ∈ ons_noncriticalNeighborhood beta) :
-- imply
  Continuous (fun p : ℝ × ℝ => Real.log (ons_gInt b p.1 p.2)) := by
-- proof
  apply StatMech.Onsager.ons_log_gInt_continuous_momenta_noncritical hbeta hcrit hb

/--
[ons_logGIntBetaDeriv_continuous_momenta_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_logGIntBetaDeriv_continuous_momenta_noncritical_eq
  {beta b : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC)
  (hb : b ∈ ons_noncriticalNeighborhood beta) :
-- imply
  Continuous (fun p : ℝ × ℝ => ons_logGIntBetaDeriv b p.1 p.2) := by
-- proof
  apply StatMech.Onsager.ons_logGIntBetaDeriv_continuous_momenta_noncritical hbeta hcrit hb

/--
[ons_hasDerivAt_innerIntegral_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_hasDerivAt_innerIntegral_noncritical_eq
  {beta k1 : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC) :
-- imply
  HasDerivAt (fun b => ∫ k2 in (-Real.pi)..Real.pi, Real.log (ons_gInt b k1 k2)) (∫ k2 in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv beta k1 k2) beta := by
-- proof
  apply StatMech.Onsager.ons_hasDerivAt_innerIntegral_noncritical beta k1 hbeta hcrit

/--
[ons_noncriticalNeighborhood_ne_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_noncriticalNeighborhood_ne_betaC_eq
  {beta b : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC)
  (hb : b ∈ ons_noncriticalNeighborhood beta) :
-- imply
  b ≠ ons_betaC := by
-- proof
  apply StatMech.Onsager.ons_noncriticalNeighborhood_ne_betaC hbeta hcrit hb

/--
[ons_innerLogIntegral_continuous_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_innerLogIntegral_continuous_noncritical_eq
  {beta b : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC)
  (hb : b ∈ ons_noncriticalNeighborhood beta) :
-- imply
  Continuous (fun k1 => ∫ k2 in (-Real.pi)..Real.pi, Real.log (ons_gInt b k1 k2)) := by
-- proof
  apply StatMech.Onsager.ons_innerLogIntegral_continuous_noncritical hbeta hcrit hb

/--
[ons_innerLogDerivIntegral_continuous_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_innerLogDerivIntegral_continuous_noncritical_eq
  {beta b : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC)
  (hb : b ∈ ons_noncriticalNeighborhood beta) :
-- imply
  Continuous (fun k1 => ∫ k2 in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv b k1 k2) := by
-- proof
  apply StatMech.Onsager.ons_innerLogDerivIntegral_continuous_noncritical hbeta hcrit hb

/--
[ons_hasDerivAt_doubleIntegral_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_hasDerivAt_doubleIntegral_noncritical_eq
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC) :
-- imply
  HasDerivAt (fun b => ∫ k1 in (-Real.pi)..Real.pi, ∫ k2 in (-Real.pi)..Real.pi, Real.log (ons_gInt b k1 k2)) (∫ k1 in (-Real.pi)..Real.pi, ∫ k2 in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv beta k1 k2) beta := by
-- proof
  apply StatMech.Onsager.ons_hasDerivAt_doubleIntegral_noncritical beta hbeta hcrit

/--
[ons_hasDerivAt_freeEnergyIntegral_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_hasDerivAt_freeEnergyIntegral_noncritical_eq
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC) :
-- imply
  HasDerivAt ons_freeEnergyIntegral ((1 / (8 * Real.pi ^ 2)) * ∫ k1 in (-Real.pi)..Real.pi, ∫ k2 in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv beta k1 k2) beta := by
-- proof
  apply StatMech.Onsager.ons_hasDerivAt_freeEnergyIntegral_noncritical beta hbeta hcrit

/--
[ons_hasDerivAt_pressure_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_hasDerivAt_pressure_noncritical_eq
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC) :
-- imply
  HasDerivAt ons_pressure ((1 / (8 * Real.pi ^ 2)) * ∫ k1 in (-Real.pi)..Real.pi, ∫ k2 in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv beta k1 k2) beta := by
-- proof
  apply StatMech.Onsager.ons_hasDerivAt_pressure_noncritical beta hbeta hcrit

/--
[ons_criticalParameterNeighborhood_mem_nhds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalParameterNeighborhood_mem_nhds_eq :
-- imply
  ons_criticalParameterNeighborhood ∈ nhds ons_betaC := by
-- proof
  apply StatMech.Onsager.ons_criticalParameterNeighborhood_mem_nhds

/--
[ons_gInt_lower_criticalNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_gInt_lower_criticalNeighborhood_eq
  {b k1 k2 : ℝ}
-- given
  (hb : b ∈ ons_criticalParameterNeighborhood) :
-- imply
  (Real.sinh (2 * b) - 1) ^ 2 + (2 - Real.cos k1 - Real.cos k2) / 4 ≤ ons_gInt b k1 k2 := by
-- proof
  apply StatMech.Onsager.ons_gInt_lower_criticalNeighborhood hb

/--
[ons_gIntBetaDeriv_abs_le_criticalNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_gIntBetaDeriv_abs_le_criticalNeighborhood_eq
  {b k1 k2 : ℝ}
-- given
  (hb : b ∈ ons_criticalParameterNeighborhood) :
-- imply
  |ons_gIntBetaDeriv b k1 k2| ≤ 4 * (2 * |Real.sinh (2 * b) - 1| + (2 - Real.cos k1 - Real.cos k2)) := by
-- proof
  apply StatMech.Onsager.ons_gIntBetaDeriv_abs_le_criticalNeighborhood hb

/--
[ons_delta_ratio_le_inv_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_delta_ratio_le_inv_sqrt_eq
  {delta A : ℝ}
-- given
  (hA : 0 < A) :
-- imply
  (2 * |delta| + A) / (delta ^ 2 + A) ≤ 1 / Real.sqrt A + 1 := by
-- proof
  apply StatMech.Onsager.ons_delta_ratio_le_inv_sqrt hA

/--
[ons_delta_ratio_quarter_le_inv_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_delta_ratio_quarter_le_inv_sqrt_eq
  {delta A : ℝ}
-- given
  (hA : 0 < A) :
-- imply
  (2 * |delta| + A) / (delta ^ 2 + A / 4) ≤ 8 * (1 / Real.sqrt A + 1) := by
-- proof
  apply StatMech.Onsager.ons_delta_ratio_quarter_le_inv_sqrt hA

/--
[ons_logGIntBetaDeriv_abs_le_criticalA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_logGIntBetaDeriv_abs_le_criticalA_eq
  {b k1 k2 : ℝ}
-- given
  (hb : b ∈ ons_criticalParameterNeighborhood)
  (hA : 0 < 2 - Real.cos k1 - Real.cos k2) :
-- imply
  |ons_logGIntBetaDeriv b k1 k2| ≤ 32 * (1 / Real.sqrt (2 - Real.cos k1 - Real.cos k2) + 1) := by
-- proof
  apply StatMech.Onsager.ons_logGIntBetaDeriv_abs_le_criticalA hb hA

/--
[ons_criticalDenom_lower_abs_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalDenom_lower_abs_mul_eq
  {x y : ℝ}
-- given
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hy : y ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  |x * y| / Real.pi ^ 2 ≤ 2 - Real.cos x - Real.cos y := by
-- proof
  apply StatMech.Onsager.ons_criticalDenom_lower_abs_mul hx hy

/--
[ons_inv_sqrt_criticalDenom_le_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_inv_sqrt_criticalDenom_le_product_eq
  {x y : ℝ}
-- given
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hy : y ∈ Set.Icc (-Real.pi) Real.pi)
  (hx0 : x ≠ 0)
  (hy0 : y ≠ 0) :
-- imply
  1 / Real.sqrt (2 - Real.cos x - Real.cos y) ≤ Real.pi * (1 / Real.sqrt |x|) * (1 / Real.sqrt |y|) := by
-- proof
  apply StatMech.Onsager.ons_inv_sqrt_criticalDenom_le_product hx hy hx0 hy0

/--
[ons_logGIntBetaDeriv_abs_le_criticalProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_logGIntBetaDeriv_abs_le_criticalProduct_eq
  {b x y : ℝ}
-- given
  (hb : b ∈ ons_criticalParameterNeighborhood)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hy : y ∈ Set.Icc (-Real.pi) Real.pi)
  (hx0 : x ≠ 0)
  (hy0 : y ≠ 0) :
-- imply
  |ons_logGIntBetaDeriv b x y| ≤ 32 * (Real.pi * (1 / Real.sqrt |x|) * (1 / Real.sqrt |y|) + 1) := by
-- proof
  apply StatMech.Onsager.ons_logGIntBetaDeriv_abs_le_criticalProduct hb hx hy hx0 hy0

/--
[ons_criticalParameterNeighborhood_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalParameterNeighborhood_isOpen_eq :
-- imply
  IsOpen ons_criticalParameterNeighborhood := by
-- proof
  apply StatMech.Onsager.ons_criticalParameterNeighborhood_isOpen

/--
[ons_one_div_sqrt_eq_rpow_neg_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_one_div_sqrt_eq_rpow_neg_half_eq
  {x : ℝ}
-- given
  (hx : 0 ≤ x) :
-- imply
  1 / Real.sqrt x = x ^ (-(1 / 2 : ℝ)) := by
-- proof
  apply StatMech.Onsager.ons_one_div_sqrt_eq_rpow_neg_half hx

/--
[ons_criticalOneDimMajorant_intervalIntegrable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalOneDimMajorant_intervalIntegrable_eq :
-- imply
  IntervalIntegrable ons_criticalOneDimMajorant MeasureTheory.volume (-Real.pi) Real.pi := by
-- proof
  apply StatMech.Onsager.ons_criticalOneDimMajorant_intervalIntegrable

/--
[ons_criticalProductMajorant_inner_intervalIntegrable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalProductMajorant_inner_intervalIntegrable_eq
  {x : ℝ} :
-- imply
  IntervalIntegrable (ons_criticalProductMajorant x) MeasureTheory.volume (-Real.pi) Real.pi := by
-- proof
  apply StatMech.Onsager.ons_criticalProductMajorant_inner_intervalIntegrable x

/--
[ons_logGIntBetaDeriv_abs_le_criticalMajorant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_logGIntBetaDeriv_abs_le_criticalMajorant_eq
  {b x y : ℝ}
-- given
  (hb : b ∈ ons_criticalParameterNeighborhood)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hy : y ∈ Set.Icc (-Real.pi) Real.pi)
  (hx0 : x ≠ 0)
  (hy0 : y ≠ 0) :
-- imply
  |ons_logGIntBetaDeriv b x y| ≤ ons_criticalProductMajorant x y := by
-- proof
  apply StatMech.Onsager.ons_logGIntBetaDeriv_abs_le_criticalMajorant hb hx hy hx0 hy0

/--
[ons_criticalDenom_pos_of_left_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalDenom_pos_of_left_ne_zero_eq
  {x y : ℝ}
-- given
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hx0 : x ≠ 0) :
-- imply
  0 < 2 - Real.cos x - Real.cos y := by
-- proof
  apply StatMech.Onsager.ons_criticalDenom_pos_of_left_ne_zero hx hx0

/--
[ons_gInt_pos_criticalNeighborhood_of_left_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_gInt_pos_criticalNeighborhood_of_left_ne_zero_eq
  {b x y : ℝ}
-- given
  (hb : b ∈ ons_criticalParameterNeighborhood)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hx0 : x ≠ 0) :
-- imply
  0 < ons_gInt b x y := by
-- proof
  apply StatMech.Onsager.ons_gInt_pos_criticalNeighborhood_of_left_ne_zero hb hx hx0

/--
[ons_log_gInt_continuous_right_criticalNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_log_gInt_continuous_right_criticalNeighborhood_eq
  {b x : ℝ}
-- given
  (hb : b ∈ ons_criticalParameterNeighborhood)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hx0 : x ≠ 0) :
-- imply
  Continuous (fun y => Real.log (ons_gInt b x y)) := by
-- proof
  apply StatMech.Onsager.ons_log_gInt_continuous_right_criticalNeighborhood hb hx hx0

/--
[ons_logGIntBetaDeriv_continuous_right_criticalNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_logGIntBetaDeriv_continuous_right_criticalNeighborhood_eq
  {b x : ℝ}
-- given
  (hb : b ∈ ons_criticalParameterNeighborhood)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hx0 : x ≠ 0) :
-- imply
  Continuous (fun y => ons_logGIntBetaDeriv b x y) := by
-- proof
  apply StatMech.Onsager.ons_logGIntBetaDeriv_continuous_right_criticalNeighborhood hb hx hx0

/--
[ons_ae_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_ae_ne_zero_eq :
-- imply
  ∀ᵐ x : ℝ ∂MeasureTheory.volume, x ≠ 0 := by
-- proof
  apply StatMech.Onsager.ons_ae_ne_zero

/--
[ons_hasDerivAt_innerIntegral_criticalNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_hasDerivAt_innerIntegral_criticalNeighborhood_eq
  {b x : ℝ}
-- given
  (hb : b ∈ ons_criticalParameterNeighborhood)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hx0 : x ≠ 0) :
-- imply
  HasDerivAt (fun beta => ∫ y in (-Real.pi)..Real.pi, Real.log (ons_gInt beta x y)) (∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv b x y) b := by
-- proof
  apply StatMech.Onsager.ons_hasDerivAt_innerIntegral_criticalNeighborhood hb hx hx0

/--
[ons_criticalParameterNeighborhood_sinh_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalParameterNeighborhood_sinh_bounds_eq
  {b : ℝ}
-- given
  (hb : b ∈ ons_criticalParameterNeighborhood) :
-- imply
  (1 / 2 : ℝ) ≤ Real.sinh (2 * b) ∧ Real.sinh (2 * b) ≤ 2 := by
-- proof
  apply StatMech.Onsager.ons_criticalParameterNeighborhood_sinh_bounds hb

/--
[ons_criticalProductMajorant_inner_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalProductMajorant_inner_integral_eq
  {x : ℝ} :
-- imply
  (∫ y in (-Real.pi)..Real.pi, ons_criticalProductMajorant x y) = 32 * (Real.pi * ons_criticalOneDimMajorant x * (∫ y in (-Real.pi)..Real.pi, ons_criticalOneDimMajorant y) + 2 * Real.pi) := by
-- proof
  apply StatMech.Onsager.ons_criticalProductMajorant_inner_integral x

/--
[ons_criticalOuterMajorant_intervalIntegrable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_criticalOuterMajorant_intervalIntegrable_eq :
-- imply
  IntervalIntegrable ons_criticalOuterMajorant MeasureTheory.volume (-Real.pi) Real.pi := by
-- proof
  apply StatMech.Onsager.ons_criticalOuterMajorant_intervalIntegrable

/--
[ons_innerLogDerivIntegral_norm_le_criticalOuterMajorant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_innerLogDerivIntegral_norm_le_criticalOuterMajorant_eq
  {b x : ℝ}
-- given
  (hb : b ∈ ons_criticalParameterNeighborhood)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hx0 : x ≠ 0) :
-- imply
  ‖∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv b x y‖ ≤ ons_criticalOuterMajorant x := by
-- proof
  apply StatMech.Onsager.ons_innerLogDerivIntegral_norm_le_criticalOuterMajorant hb hx hx0

/--
[ons_hasDerivAt_doubleIntegral_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_hasDerivAt_doubleIntegral_betaC_eq :
-- imply
  HasDerivAt (fun b => ∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi, Real.log (ons_gInt b x y)) (∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv ons_betaC x y) ons_betaC := by
-- proof
  apply StatMech.Onsager.ons_hasDerivAt_doubleIntegral_betaC

/--
[ons_hasDerivAt_freeEnergyIntegral_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_hasDerivAt_freeEnergyIntegral_betaC_eq :
-- imply
  HasDerivAt ons_freeEnergyIntegral (Real.sqrt 2) ons_betaC := by
-- proof
  apply StatMech.Onsager.ons_hasDerivAt_freeEnergyIntegral_betaC

/--
[ons_hasDerivAt_pressure_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_hasDerivAt_pressure_betaC_eq :
-- imply
  HasDerivAt ons_pressure (Real.sqrt 2) ons_betaC := by
-- proof
  apply StatMech.Onsager.ons_hasDerivAt_pressure_betaC

/--
[ons_innerLogDerivIntegral_aestronglyMeasurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_innerLogDerivIntegral_aestronglyMeasurable_eq
  {b : ℝ} :
-- imply
  MeasureTheory.AEStronglyMeasurable (fun x => ∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv b x y) (MeasureTheory.volume.restrict (Set.uIoc (-Real.pi) Real.pi)) := by
-- proof
  apply StatMech.Onsager.ons_innerLogDerivIntegral_aestronglyMeasurable b

/--
[ons_innerLogDerivIntegral_continuousAt_criticalNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_innerLogDerivIntegral_continuousAt_criticalNeighborhood_eq
  {b x : ℝ}
-- given
  (hb : b ∈ ons_criticalParameterNeighborhood)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hx0 : x ≠ 0) :
-- imply
  ContinuousAt (fun beta => ∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv beta x y) b := by
-- proof
  apply StatMech.Onsager.ons_innerLogDerivIntegral_continuousAt_criticalNeighborhood hb hx hx0

/--
[ons_firstDerivativeDoubleIntegral_continuousAt_criticalNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_firstDerivativeDoubleIntegral_continuousAt_criticalNeighborhood_eq
  {b : ℝ}
-- given
  (hb : b ∈ ons_criticalParameterNeighborhood) :
-- imply
  ContinuousAt (fun beta => ∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv beta x y) b := by
-- proof
  apply StatMech.Onsager.ons_firstDerivativeDoubleIntegral_continuousAt_criticalNeighborhood hb

/--
[ons_firstDerivativeDoubleIntegral_continuousOn_criticalNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_firstDerivativeDoubleIntegral_continuousOn_criticalNeighborhood_eq :
-- imply
  ContinuousOn (fun beta => ∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv beta x y) ons_criticalParameterNeighborhood := by
-- proof
  apply StatMech.Onsager.ons_firstDerivativeDoubleIntegral_continuousOn_criticalNeighborhood

/--
[ons_hasDerivAt_doubleIntegral_criticalNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_hasDerivAt_doubleIntegral_criticalNeighborhood_eq
  {b : ℝ}
-- given
  (hb : b ∈ ons_criticalParameterNeighborhood) :
-- imply
  HasDerivAt (fun beta => ∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi, Real.log (ons_gInt beta x y)) (∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv b x y) b := by
-- proof
  apply StatMech.Onsager.ons_hasDerivAt_doubleIntegral_criticalNeighborhood hb

/--
[ons_hasDerivAt_freeEnergyIntegral_criticalNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_hasDerivAt_freeEnergyIntegral_criticalNeighborhood_eq
  {b : ℝ}
-- given
  (hb : b ∈ ons_criticalParameterNeighborhood) :
-- imply
  HasDerivAt ons_freeEnergyIntegral ((1 / (8 * Real.pi ^ 2)) * ∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv b x y) b := by
-- proof
  apply StatMech.Onsager.ons_hasDerivAt_freeEnergyIntegral_criticalNeighborhood hb

/--
[ons_hasDerivAt_pressure_criticalNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_hasDerivAt_pressure_criticalNeighborhood_eq
  {b : ℝ}
-- given
  (hb : b ∈ ons_criticalParameterNeighborhood) :
-- imply
  HasDerivAt ons_pressure ((1 / (8 * Real.pi ^ 2)) * ∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv b x y) b := by
-- proof
  apply StatMech.Onsager.ons_hasDerivAt_pressure_criticalNeighborhood hb

/--
[ons_pressure_contDiffAt_one_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_pressure_contDiffAt_one_betaC_eq :
-- imply
  ContDiffAt ℝ 1 ons_pressure ons_betaC := by
-- proof
  apply StatMech.Onsager.ons_pressure_contDiffAt_one_betaC

/--
[ons_gIntComplex_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_gIntComplex_ofReal_eq
  {beta k1 k2 : ℝ} :
-- imply
  ons_gIntComplex (beta : ℂ) k1 k2 = (ons_gInt beta k1 k2 : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_gIntComplex_ofReal beta k1 k2

/--
[ons_complexNoncriticalDeviation_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_complexNoncriticalDeviation_continuous_eq
  {beta : ℝ} :
-- imply
  Continuous (ons_complexNoncriticalDeviation beta) := by
-- proof
  apply StatMech.Onsager.ons_complexNoncriticalDeviation_continuous beta

/--
[ons_complexCoshNorm_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_complexCoshNorm_continuous_eq :
-- imply
  Continuous (fun z : ℂ => ‖Complex.cosh (2 * z)‖) := by
-- proof
  apply StatMech.Onsager.ons_complexCoshNorm_continuous

/--
[ons_complexSinhNorm_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_complexSinhNorm_continuous_eq :
-- imply
  Continuous (fun z : ℂ => ‖Complex.sinh (2 * z)‖) := by
-- proof
  apply StatMech.Onsager.ons_complexSinhNorm_continuous

/--
[ons_complexNoncriticalDeviation_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_complexNoncriticalDeviation_ofReal_eq
  {beta : ℝ} :
-- imply
  ons_complexNoncriticalDeviation beta (beta : ℂ) = 0 := by
-- proof
  apply StatMech.Onsager.ons_complexNoncriticalDeviation_ofReal beta

/--
[ons_complexNoncriticalNeighborhood_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_complexNoncriticalNeighborhood_isOpen_eq
  {beta : ℝ} :
-- imply
  IsOpen (ons_complexNoncriticalNeighborhood beta) := by
-- proof
  apply StatMech.Onsager.ons_complexNoncriticalNeighborhood_isOpen beta

/--
[ons_complexNoncriticalNeighborhood_mem_nhds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_complexNoncriticalNeighborhood_mem_nhds_eq
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC) :
-- imply
  ons_complexNoncriticalNeighborhood beta ∈ nhds (beta : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_complexNoncriticalNeighborhood_mem_nhds hbeta hcrit

/--
[ons_gIntComplex_sub_ofReal_norm_le_deviation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_gIntComplex_sub_ofReal_norm_le_deviation_eq
  {beta : ℝ}
  {z : ℂ}
  {k1 k2 : ℝ} :
-- imply
  ‖ons_gIntComplex z k1 k2 - (ons_gInt beta k1 k2 : ℂ)‖ ≤ ons_complexNoncriticalDeviation beta z := by
-- proof
  apply StatMech.Onsager.ons_gIntComplex_sub_ofReal_norm_le_deviation beta z k1 k2

/--
[ons_gInt_lower_noncritical_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_gInt_lower_noncritical_base_eq
  {beta k1 k2 : ℝ}
-- given
  (hbeta : 0 < beta)
  (_hcrit : beta ≠ ons_betaC) :
-- imply
  ons_noncriticalGap beta ^ 2 ≤ ons_gInt beta k1 k2 := by
-- proof
  apply StatMech.Onsager.ons_gInt_lower_noncritical_base hbeta _hcrit

/--
[ons_gIntComplex_re_pos_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_gIntComplex_re_pos_noncritical_eq
  {beta : ℝ}
  {z : ℂ}
  {k1 k2 : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC)
  (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
-- imply
  0 < (ons_gIntComplex z k1 k2).re := by
-- proof
  apply StatMech.Onsager.ons_gIntComplex_re_pos_noncritical hbeta hcrit hz k1 k2

/--
[ons_gIntComplex_mem_slitPlane_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_gIntComplex_mem_slitPlane_noncritical_eq
  {beta : ℝ}
  {z : ℂ}
  {k1 k2 : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC)
  (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
-- imply
  ons_gIntComplex z k1 k2 ∈ Complex.slitPlane := by
-- proof
  apply StatMech.Onsager.ons_gIntComplex_mem_slitPlane_noncritical hbeta hcrit hz k1 k2

/--
[ons_gIntComplex_norm_lower_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_gIntComplex_norm_lower_noncritical_eq
  {beta : ℝ}
  {z : ℂ}
  {k1 k2 : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC)
  (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
-- imply
  ons_noncriticalGap beta ^ 2 / 2 < ‖ons_gIntComplex z k1 k2‖ := by
-- proof
  apply StatMech.Onsager.ons_gIntComplex_norm_lower_noncritical hbeta hcrit hz k1 k2

/--
[ons_logGIntComplexDeriv_norm_le_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_logGIntComplexDeriv_norm_le_noncritical_eq
  {beta : ℝ}
  {z : ℂ}
  {k1 k2 : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC)
  (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
-- imply
  ‖ons_logGIntComplexDeriv z k1 k2‖ ≤ (2 * (|Real.cosh (2 * beta)| + 1) * (2 * (|Real.sinh (2 * beta)| + 1) + 2)) / (ons_noncriticalGap beta ^ 2 / 2) := by
-- proof
  apply StatMech.Onsager.ons_logGIntComplexDeriv_norm_le_noncritical hbeta hcrit hz k1 k2

/--
[ons_hasDerivAt_gIntComplex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_hasDerivAt_gIntComplex_eq
  {z : ℂ}
  {k1 k2 : ℝ} :
-- imply
  HasDerivAt (fun w => ons_gIntComplex w k1 k2) (ons_gIntComplexDeriv z k1 k2) z := by
-- proof
  apply StatMech.Onsager.ons_hasDerivAt_gIntComplex z k1 k2

/--
[ons_hasDerivAt_log_gIntComplex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_hasDerivAt_log_gIntComplex_eq
  {beta : ℝ}
  {z : ℂ}
  {k1 k2 : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC)
  (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
-- imply
  HasDerivAt (fun w => Complex.log (ons_gIntComplex w k1 k2)) (ons_logGIntComplexDeriv z k1 k2) z := by
-- proof
  apply StatMech.Onsager.ons_hasDerivAt_log_gIntComplex hbeta hcrit hz k1 k2

/--
[ons_complexLogGInt_continuous_momenta_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_complexLogGInt_continuous_momenta_noncritical_eq
  {beta : ℝ}
  {z : ℂ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC)
  (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
-- imply
  Continuous (fun p : ℝ × ℝ => Complex.log (ons_gIntComplex z p.1 p.2)) := by
-- proof
  apply StatMech.Onsager.ons_complexLogGInt_continuous_momenta_noncritical hbeta hcrit hz

/--
[ons_logGIntComplexDeriv_continuous_momenta_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_logGIntComplexDeriv_continuous_momenta_noncritical_eq
  {beta : ℝ}
  {z : ℂ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC)
  (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
-- imply
  Continuous (fun p : ℝ × ℝ => ons_logGIntComplexDeriv z p.1 p.2) := by
-- proof
  apply StatMech.Onsager.ons_logGIntComplexDeriv_continuous_momenta_noncritical hbeta hcrit hz

/--
[ons_complexInnerLogIntegral_continuous_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_complexInnerLogIntegral_continuous_noncritical_eq
  {beta : ℝ}
  {z : ℂ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC)
  (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
-- imply
  Continuous (fun k1 => ∫ k2 in (-Real.pi)..Real.pi, Complex.log (ons_gIntComplex z k1 k2)) := by
-- proof
  apply StatMech.Onsager.ons_complexInnerLogIntegral_continuous_noncritical hbeta hcrit hz

/--
[ons_complexInnerLogDerivIntegral_continuous_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_complexInnerLogDerivIntegral_continuous_noncritical_eq
  {beta : ℝ}
  {z : ℂ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC)
  (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
-- imply
  Continuous (fun k1 => ∫ k2 in (-Real.pi)..Real.pi, ons_logGIntComplexDeriv z k1 k2) := by
-- proof
  apply StatMech.Onsager.ons_complexInnerLogDerivIntegral_continuous_noncritical hbeta hcrit hz

/--
[ons_hasDerivAt_complexInnerIntegral_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_hasDerivAt_complexInnerIntegral_noncritical_eq
  {beta : ℝ}
  {z : ℂ}
  {k1 : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC)
  (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
-- imply
  HasDerivAt (fun w => ∫ k2 in (-Real.pi)..Real.pi, Complex.log (ons_gIntComplex w k1 k2)) (∫ k2 in (-Real.pi)..Real.pi, ons_logGIntComplexDeriv z k1 k2) z := by
-- proof
  apply StatMech.Onsager.ons_hasDerivAt_complexInnerIntegral_noncritical k1 hbeta hcrit hz

/--
[ons_hasDerivAt_complexDoubleIntegral_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_hasDerivAt_complexDoubleIntegral_noncritical_eq
  {beta : ℝ}
  {z : ℂ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC)
  (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
-- imply
  HasDerivAt (fun w => ∫ k1 in (-Real.pi)..Real.pi, ∫ k2 in (-Real.pi)..Real.pi, Complex.log (ons_gIntComplex w k1 k2)) (∫ k1 in (-Real.pi)..Real.pi, ∫ k2 in (-Real.pi)..Real.pi, ons_logGIntComplexDeriv z k1 k2) z := by
-- proof
  apply StatMech.Onsager.ons_hasDerivAt_complexDoubleIntegral_noncritical hbeta hcrit hz

/--
[ons_pressureComplex_differentiableOn_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_pressureComplex_differentiableOn_noncritical_eq
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC) :
-- imply
  DifferentiableOn ℂ ons_pressureComplex (ons_complexNoncriticalNeighborhood beta) := by
-- proof
  apply StatMech.Onsager.ons_pressureComplex_differentiableOn_noncritical hbeta hcrit

/--
[ons_pressureComplex_analyticAt_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_pressureComplex_analyticAt_noncritical_eq
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC) :
-- imply
  AnalyticAt ℂ ons_pressureComplex (beta : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_pressureComplex_analyticAt_noncritical hbeta hcrit

/--
[ons_complexLogGInt_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_complexLogGInt_ofReal_eq
  {beta : ℝ}
  {k1 k2 : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC) :
-- imply
  Complex.log (ons_gIntComplex (beta : ℂ) k1 k2) = (Real.log (ons_gInt beta k1 k2) : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_complexLogGInt_ofReal hbeta hcrit k1 k2

/--
[ons_complexDoubleIntegral_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_complexDoubleIntegral_ofReal_eq
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC) :
-- imply
  (∫ k1 in (-Real.pi)..Real.pi, ∫ k2 in (-Real.pi)..Real.pi, Complex.log (ons_gIntComplex (beta : ℂ) k1 k2)) = Complex.ofReal (∫ k1 in (-Real.pi)..Real.pi, ∫ k2 in (-Real.pi)..Real.pi, Real.log (ons_gInt beta k1 k2)) := by
-- proof
  apply StatMech.Onsager.ons_complexDoubleIntegral_ofReal hbeta hcrit

/--
[ons_pressureComplex_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_pressureComplex_ofReal_eq
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC) :
-- imply
  ons_pressureComplex (beta : ℂ) = (ons_pressure beta : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_pressureComplex_ofReal hbeta hcrit

/--
[ons_pressure_analyticAt_noncritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_pressure_analyticAt_noncritical_eq
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hcrit : beta ≠ ons_betaC) :
-- imply
  AnalyticAt ℝ ons_pressure beta := by
-- proof
  apply StatMech.Onsager.ons_pressure_analyticAt_noncritical hbeta hcrit

/--
[ons_phase_regularity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean)
-/
@[path]
private lemma ons_phase_regularity_eq :
-- imply
  (∀ beta : ℝ, 0 < beta → beta ≠ ons_betaC → AnalyticAt ℝ ons_pressure beta) ∧ ContDiffAt ℝ 1 ons_pressure ons_betaC ∧ HasDerivAt ons_pressure (Real.sqrt 2) ons_betaC ∧ (∀ n : ℕ, -4 + (32 / 5 : ℝ) * (n : ℝ) ≤ ∫ x in Real.exp (-(n : ℝ))..1, ∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y) ∧ Filter.Tendsto (fun n : ℕ => (∫ x in (-Real.pi)..(-Real.exp (-(n : ℝ))), ∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y) + ∫ x in Real.exp (-(n : ℝ))..Real.pi, ∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y) Filter.atTop Filter.atTop := by
-- proof
  apply StatMech.Onsager.ons_phase_regularity


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.ContinuousFKG.Part3
open MeasureTheory StatMech StatMech.Probability


/--
[ContinuousFKG.integrable_of_bdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKG.lean)
-/
@[path]
private lemma integrable_of_bdd_eq
  [MeasurableSpace α]
  {μ : Measure α}
  [IsFiniteMeasure μ]
  {f : α → ℝ}
  {C : ℝ}
-- given
  (hf : Measurable f)
  (hC : ∀ x, |f x| ≤ C) :
-- imply
  Integrable f μ := by
-- proof
  apply StatMech.Probability.ContinuousFKG.integrable_of_bdd μ hf hC

/--
[ContinuousFKG.comonotone_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKG.lean)
-/
@[path]
private lemma comonotone_nonneg_eq
  {f g : ℝ → ℝ}
  {x y : ℝ}
-- given
  (hf : Monotone f)
  (hg : Monotone g) :
-- imply
  0 ≤ (f x - f y) * (g x - g y) := by
-- proof
  apply StatMech.Probability.ContinuousFKG.comonotone_nonneg hf hg x y

/--
[chebyshev_correlation_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKG.lean)
-/
@[path]
private lemma chebyshev_correlation_prob_eq
  {μ : Measure ℝ}
  [IsProbabilityMeasure μ]
  {f g : ℝ → ℝ}
  {Cf Cg : ℝ}
-- given
  (hfm : Measurable f)
  (hgm : Measurable g)
  (hfC : ∀ x, |f x| ≤ Cf)
  (hgC : ∀ x, |g x| ≤ Cg)
  (hf : Monotone f)
  (hg : Monotone g) :
-- imply
  (∫ x, f x ∂μ) * (∫ x, g x ∂μ) ≤ ∫ x, f x * g x ∂μ := by
-- proof
  apply StatMech.Probability.chebyshev_correlation_prob μ hfm hgm hfC hgC hf hg

/--
[hasFKG_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKG.lean)
-/
@[path]
private lemma hasFKG_real_eq
  {μ : Measure ℝ}
  [IsProbabilityMeasure μ] :
-- imply
  HasFKG μ := by
-- proof
  apply StatMech.Probability.hasFKG_real μ

/--
[hasFKG_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKG.lean)
-/
@[path]
private lemma hasFKG_subsingleton_eq
  [MeasurableSpace β]
  [Preorder β]
  [Subsingleton β]
  {ν : Measure β}
  [IsProbabilityMeasure ν] :
-- imply
  HasFKG ν := by
-- proof
  apply StatMech.Probability.hasFKG_subsingleton ν

/--
[prod_fkg_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKG.lean)
-/
@[path]
private lemma prod_fkg_step_eq
  [MeasurableSpace β]
  [Preorder β]
  {μ : Measure ℝ}
  [IsProbabilityMeasure μ]
  {ν : Measure β}
  [IsProbabilityMeasure ν]
-- given
  (hcheb : HasFKG μ)
  (hν : HasFKG ν) :
-- imply
  HasFKG (μ.prod ν) := by
-- proof
  apply StatMech.Probability.prod_fkg_step μ ν hcheb hν

/--
[hasFKG_of_orderIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKG.lean)
-/
@[path]
private lemma hasFKG_of_orderIso_eq
  [MeasurableSpace β]
  [Preorder β]
  [MeasurableSpace γ]
  [Preorder γ]
  {μ : Measure β}
  {ν : Measure γ}
  {e : β ≃ᵐ γ}
-- given
  (hmp : MeasurePreserving e μ ν)
  (hmonoinv : Monotone e.symm)
  (hν : HasFKG ν) :
-- imply
  HasFKG μ := by
-- proof
  apply StatMech.Probability.hasFKG_of_orderIso μ ν e hmp hmonoinv hν

/--
[piFinSuccAbove_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKG.lean)
-/
@[path]
private lemma piFinSuccAbove_reflect_eq
  {n : ℕ}
  {x y : Fin (n + 1) → ℝ}
-- given
  (h : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) x ≤ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) y) :
-- imply
  x ≤ y := by
-- proof
  apply StatMech.Probability.piFinSuccAbove_reflect n x y h

/--
[piFinSuccAbove_symm_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKG.lean)
-/
@[path]
private lemma piFinSuccAbove_symm_mono_eq
  {n : ℕ} :
-- imply
  Monotone (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm := by
-- proof
  apply StatMech.Probability.piFinSuccAbove_symm_mono n

/--
[hasFKG_pi_unitMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKG.lean)
-/
@[path]
private lemma hasFKG_pi_unitMeasure_eq
  {n : ℕ} :
-- imply
  HasFKG (Measure.pi (fun _ : Fin n => unitMeasure)) := by
-- proof
  apply StatMech.Probability.hasFKG_pi_unitMeasure n

/--
[continuous_fkg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKG.lean)
-/
@[path]
private lemma continuous_fkg_eq
  {n : ℕ}
  {f g : (Fin n → ℝ) → ℝ}
  {Cf Cg : ℝ}
-- given
  (hfm : Measurable f)
  (hgm : Measurable g)
  (hfC : ∀ x, |f x| ≤ Cf)
  (hgC : ∀ x, |g x| ≤ Cg)
  (hf : Monotone f)
  (hg : Monotone g) :
-- imply
  (∫ x, f x ∂(Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)))) * (∫ x, g x ∂(Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)))) ≤ ∫ x, f x * g x ∂(Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))) := by
-- proof
  apply StatMech.Probability.continuous_fkg n hfm hgm hfC hgC hf hg


-- created on 2026-10-23

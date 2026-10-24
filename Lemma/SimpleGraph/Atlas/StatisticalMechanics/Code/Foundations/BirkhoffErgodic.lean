import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Foundations.BirkhoffErgodic
open MeasureTheory Filter Finset Function MeasurableSpace StatMech StatMech.BirkhoffAE StatMech.BirkhoffAE.Ergodic


/--
[birkhoffLimit_ae_eq_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffErgodic.lean)
-/
@[path]
private lemma birkhoffLimit_ae_eq_const_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsProbabilityMeasure μ]
-- given
  (hT : _root_.Ergodic T μ)
  (hf : Integrable f μ) :
-- imply
  birkhoffLimit T f =ᵐ[μ] Function.const α (∫ x, f x ∂μ) := by
-- proof
  apply StatMech.BirkhoffAE.Ergodic.birkhoffLimit_ae_eq_const hT hf

/--
[tendsto_birkhoffAverage_integral_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffErgodic.lean)
-/
@[path]
private lemma tendsto_birkhoffAverage_integral_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsProbabilityMeasure μ]
-- given
  (hT : _root_.Ergodic T μ)
  (hf : Integrable f μ) :
-- imply
  ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 (∫ y, f y ∂μ)) := by
-- proof
  apply StatMech.BirkhoffAE.Ergodic.tendsto_birkhoffAverage_integral_ae hT hf

/--
[tendsto_birkhoffSum_div_integral_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffErgodic.lean)
-/
@[path]
private lemma tendsto_birkhoffSum_div_integral_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {f : α → ℝ}
  [IsProbabilityMeasure μ]
-- given
  (hT : _root_.Ergodic T μ)
  (hf : Integrable f μ) :
-- imply
  ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f (T^[k] x)) atTop (𝓝 (∫ y, f y ∂μ)) := by
-- proof
  apply StatMech.BirkhoffAE.Ergodic.tendsto_birkhoffSum_div_integral_ae hT hf


-- created on 2026-10-23

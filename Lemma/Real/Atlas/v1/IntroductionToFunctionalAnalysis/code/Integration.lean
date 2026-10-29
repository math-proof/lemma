import Mathlib
import Initialize.Tactic.Attr.Basic
open ENNReal Filter Set
open scoped Topology


namespace MeasureTheory

/--
[triangle_inequality_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/Integration.lean)
-/
@[path]
lemma triangle_inequality_integral
  [MeasurableSpace α]
  {μ : Measure α}
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  {f : α → F} :
-- imply
  ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ :=
-- proof
  norm_integral_le_integral_norm f

end MeasureTheory

namespace MeasureTheory

/--
[integral_properties](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/Integration.lean)
-/
@[path]
lemma integral_properties
  [MeasurableSpace α]
  {μ : Measure α} :
-- imply
  (∀ f : α → ℝ, Integrable f μ → ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ) ∧
  (∀ f g : α → ℝ, Integrable g μ → f =ᵐ[μ] g → Integrable f μ ∧ ∫ x, f x ∂μ = ∫ x, g x ∂μ) ∧
  (∀ f g : α → ℝ, Integrable f μ → Integrable g μ → f ≤ᵐ[μ] g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ) :=
-- proof
  ⟨fun f _ => norm_integral_le_integral_norm f,
    fun _ _ hg hfg => ⟨hg.congr hfg.symm, integral_congr_ae hfg⟩,
    fun _ _ hf hg hle => integral_mono_ae hf hg hle⟩

end MeasureTheory

namespace MeasureTheory

/--
[lintegral_add_of_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/Integration.lean)
-/
@[path]
lemma lintegral_add_of_measurable
  [MeasurableSpace α]
  {μ : Measure α}
  {f g : α → ENNReal}
-- given
  (hf : Measurable f)
  (_hg : Measurable g) :
-- imply
  ∫⁻ a, (f a + g a) ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ :=
-- proof
  lintegral_add_left hf g

end MeasureTheory

namespace MeasureTheory

/--
[monotone_convergence_lintegral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/Integration.lean)
-/
@[path]
lemma monotone_convergence_lintegral
  [MeasurableSpace α]
  {μ : Measure α}
  {f : ℕ → α → ENNReal}
-- given
  (hf : ∀ n, Measurable (f n))
  (h_mono : Monotone f) :
-- imply
  ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ :=
-- proof
  lintegral_iSup hf h_mono

end MeasureTheory

namespace MeasureTheory

/--
[monotone_convergence_lintegral_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/Integration.lean)
-/
@[path]
lemma monotone_convergence_lintegral_tendsto
  [MeasurableSpace α]
  {μ : Measure α}
  {f : ℕ → α → ENNReal}
  {g : α → ENNReal}
-- given
  (hf : ∀ n, Measurable (f n))
  (h_mono : Monotone f)
  (h_lim : ∀ a, Tendsto (fun n => f n a) atTop (nhds (g a))) :
-- imply
  Tendsto (fun n => ∫⁻ a, f n a ∂μ) atTop (nhds (∫⁻ a, g a ∂μ)) := by
-- proof
  have h_eq : (fun a => ⨆ n, f n a) = g := by
    funext a
    exact tendsto_nhds_unique
      (tendsto_atTop_iSup (fun n m hnm => h_mono hnm a))
      (h_lim a)
  conv_rhs => rw [← h_eq]
  simp_rw [monotone_convergence_lintegral hf h_mono]
  exact tendsto_atTop_iSup (fun n m hnm => lintegral_mono (h_mono hnm))

end MeasureTheory

namespace MeasureTheory

/--
[fatou_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/Integration.lean)
-/
@[path]
lemma fatou_lemma
  [MeasurableSpace α]
  {μ : Measure α}
  {f : ℕ → α → ENNReal}
-- given
  (hf : ∀ n, Measurable (f n)) :
-- imply
  ∫⁻ a, liminf (fun n => f n a) atTop ∂μ ≤ liminf (fun n => ∫⁻ a, f n a ∂μ) atTop :=
-- proof
  lintegral_liminf_le hf

end MeasureTheory

namespace MeasureTheory

/--
[measure_setOf_eq_top_of_lintegral_lt_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/Integration.lean)
-/
@[path]
lemma measure_setOf_eq_top_of_lintegral_lt_top
  [MeasurableSpace α]
  {μ : Measure α}
  {f : α → ENNReal}
-- given
  (hf : Measurable f)
  (hfint : ∫⁻ x, f x ∂μ < ⊤) :
-- imply
  μ {x | f x = ⊤} = 0 :=
-- proof
  measure_eq_top_of_lintegral_ne_top hf.aemeasurable hfint.ne

end MeasureTheory

namespace MeasureTheory

/--
[riemann_lebesgue_agree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/Integration.lean)
-/
@[path]
lemma riemann_lebesgue_agree
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  {f : ℝ → F}
  {a b : ℝ}
-- given
  (hab : a < b)
  (hf : ContinuousOn f (Icc a b)) :
-- imply
  IntegrableOn f (Icc a b) volume ∧
    IntervalIntegrable f volume a b ∧
    ∫ x in Icc a b, f x ∂volume = ∫ x in a..b, f x := by
-- proof
  refine ⟨hf.integrableOn_Icc, hf.intervalIntegrable_of_Icc hab.le, ?_⟩
  rw [intervalIntegral.integral_of_le hab.le, integral_Icc_eq_integral_Ioc]

end MeasureTheory

namespace MeasureTheory

/--
[dominated_convergence_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/Integration.lean)
-/
@[path]
lemma dominated_convergence_theorem
  [MeasurableSpace α]
  {μ : Measure α}
  [NormedAddCommGroup G]
  [NormedSpace ℝ G]
  {F : ℕ → α → G}
  {f : α → G}
  {g : α → ℝ}
-- given
  (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
  (hg_integrable : Integrable g μ)
  (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ g a)
  (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
-- imply
  Integrable f μ ∧ Tendsto (fun n => ∫ a, F n a ∂μ) atTop (𝓝 (∫ a, f a ∂μ)) := by
-- proof
  have hf_meas : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hF_meas h_lim
  have hf_bound : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a := by
    have h_all := eventually_countable_forall.mpr h_bound
    filter_upwards [h_all, h_lim] with a ha_bound ha_lim
    exact le_of_tendsto ha_lim.norm (Eventually.of_forall ha_bound)
  exact ⟨hg_integrable.mono' hf_meas hf_bound,
    tendsto_integral_of_dominated_convergence g hF_meas hg_integrable h_bound h_lim⟩

end MeasureTheory

namespace Integration

/--
[integral_eq_posPart_sub_negPart](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/Integration.lean)
-/
@[path]
lemma integral_eq_posPart_sub_negPart
  [MeasurableSpace α]
  {μ : MeasureTheory.Measure α}
  {f : α → ℝ}
-- given
  (hf : MeasureTheory.Integrable f μ) :
-- imply
  ∫ x, f x ∂μ = ∫ x, (f x)⁺ ∂μ - ∫ x, (f x)⁻ ∂μ :=
-- proof
  MeasureTheory.integral_eq_integral_pos_part_sub_integral_neg_part hf

end Integration


-- created on 2026-10-23
-- updated on 2026-10-26

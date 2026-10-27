import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.TheoryOfProbability.code.BackwardsMartingales.Part2
open MeasureTheory Filter TheoryOfProbability3
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology


namespace TheoryOfProbability3

/--
[DecreasingFiltration.tailAlgebra_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/BackwardsMartingales.lean)
-/
@[path]
lemma DecreasingFiltration.tailAlgebra_le
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  {ℱ : DecreasingFiltration Ω m0} :
-- imply
  ℱ.tailAlgebra ≤ m0 :=
-- proof
  le_trans (iInf_le _ 0) (ℱ.le' 0)

end TheoryOfProbability3

namespace TheoryOfProbability3

/--
[DecreasingFiltration.tailAlgebra_le_seq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/BackwardsMartingales.lean)
-/
@[path]
lemma DecreasingFiltration.tailAlgebra_le_seq
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  {ℱ : DecreasingFiltration Ω m0}
  {n : ℕ} :
-- imply
  ℱ.tailAlgebra ≤ ℱ.seq n :=
-- proof
  iInf_le _ n

end TheoryOfProbability3

namespace TheoryOfProbability3

/--
[IsBackwardsMartingale.integrable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/BackwardsMartingales.lean)
-/
@[path]
lemma IsBackwardsMartingale.integrable
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsFiniteMeasure μ]
  {M : ℕ → Ω → ℝ}
  {ℱ : DecreasingFiltration Ω m0}
  {n : ℕ}
-- given
  (hM : IsBackwardsMartingale M ℱ μ) :
-- imply
  Integrable (M n) μ := by
-- proof
  rwa [integrable_congr (hM.condExp_ae_eq n)]

end TheoryOfProbability3

namespace TheoryOfProbability3

/--
[IsBackwardsMartingale.uniformIntegrable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/BackwardsMartingales.lean)
-/
@[path]
lemma IsBackwardsMartingale.uniformIntegrable
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsFiniteMeasure μ]
  {M : ℕ → Ω → ℝ}
  {ℱ : DecreasingFiltration Ω m0}
-- given
  (hM : IsBackwardsMartingale M ℱ μ) :
-- imply
  UniformIntegrable M 1 μ :=
-- proof
  (hM.integrable_zero.uniformIntegrable_condExp ℱ.le').ae_eq
    (fun n => (hM.condExp_ae_eq n).symm)

end TheoryOfProbability3

namespace TheoryOfProbability3

/--
[condExp_antitone_limit_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/BackwardsMartingales.lean)
-/
@[path]
lemma condExp_antitone_limit_eq
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsFiniteMeasure μ]
  {g : Ω → ℝ}
  {m : ℕ → MeasurableSpace Ω}
-- given
  (hm_le : ∀ n, m n ≤ m0)
  (hg : Integrable g μ)
  (h : Ω → ℝ)
  (hh_ae : ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[g | m n]) ω) atTop (𝓝 (h ω)))
  (hh_int : Integrable h μ)
  (hh_meas : StronglyMeasurable[⨅ n, m n] h) :
-- imply
  h =ᵐ[μ] μ[g | ⨅ n, m n] := by
-- proof
  have hm_inf_le : ⨅ n, m n ≤ m0 := le_trans (iInf_le _ 0) (hm_le 0)
  refine ae_eq_condExp_of_forall_setIntegral_eq hm_inf_le hg
    (fun s _ _ => hh_int.integrableOn) ?_ hh_meas.aestronglyMeasurable
  intro s hs hμs
  have hs_n : ∀ n, MeasurableSet[m n] s := fun n => (iInf_le m n) s hs
  have hint_eq : ∀ n, ∫ x in s, (μ[g | m n]) x ∂μ = ∫ x in s, g x ∂μ :=
    fun n => setIntegral_condExp (hm_le n) hg (hs_n n)
  have hui : UniformIntegrable (fun n => (μ[g | m n] : Ω → ℝ)) 1 μ :=
    hg.uniformIntegrable_condExp (ℱ := m) hm_le
  have haem : ∀ n, AEStronglyMeasurable (fun ω => (μ[g | m n]) ω) μ :=
    fun n => (stronglyMeasurable_condExp (m := m n)).aestronglyMeasurable.mono (hm_le n)
  have hL1 : Tendsto (fun n => eLpNorm ((fun ω => (μ[g | m n]) ω) - h) 1 μ) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top haem
      (memLp_one_iff_integrable.mpr hh_int) hui.2.1
      (tendstoInMeasure_of_tendsto_ae haem hh_ae)
  have hL1' : Tendsto (fun n => ∫⁻ x, ‖(μ[g | m n]) x - h x‖ₑ ∂μ) atTop (𝓝 0) := by
    simp_rw [← eLpNorm_one_eq_lintegral_enorm]; convert hL1 using 1
  have hsetint := tendsto_setIntegral_of_L1 h hh_int
    (Filter.Eventually.of_forall fun n => integrable_condExp) hL1' s
  exact tendsto_nhds_unique (hsetint.congr hint_eq) tendsto_const_nhds
/-- Existence of an a.e. limit for conditional expectations along a decreasing
sequence of σ-algebras. Given any integrable `g` and antitone `m : ℕ →
MeasurableSpace Ω` with `m n ≤ m0`, there exists an integrable function `h`
measurable with respect to `⨅ n, m n` such that `μ[g | m n] → h` `μ`-a.e. -/

end TheoryOfProbability3


-- created on 2026-10-23

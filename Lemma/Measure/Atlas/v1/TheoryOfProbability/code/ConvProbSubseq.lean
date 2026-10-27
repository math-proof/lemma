import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory Filter Set MeasurableSpace
open scoped ENNReal NNReal Topology MeasureTheory


/--
[convergence_in_prob_iff_subseq_ae_real](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/ConvProbSubseq.lean)
-/
@[path]
lemma convergence_in_prob_iff_subseq_ae_real
  {m : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsFiniteMeasure μ]
  {X : ℕ → Ω → ℝ}
  {Y : Ω → ℝ}
-- given
  (hX : ∀ n, AEStronglyMeasurable (X n) μ) :
-- imply
  (∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ {ω | ε < |X n ω - Y ω|}) atTop (𝓝 0)) ↔ (∀ ns : ℕ → ℕ, StrictMono ns → ∃ ns' : ℕ → ℕ, StrictMono ns' ∧ ∀ᵐ ω ∂μ, Tendsto (fun k => X (ns (ns' k)) ω) atTop (𝓝 (Y ω))) := by
-- proof
  constructor
  ·
    intro hconv
    have hTIM : TendstoInMeasure μ X atTop Y := by
      rw [tendstoInMeasure_iff_enorm]
      intro ε hε hε_top
      set δ := ε.toReal
      have hδ_pos : 0 < δ := ENNReal.toReal_pos hε.ne' hε_top
      have hδ2_pos : 0 < δ / 2 := half_pos hδ_pos
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hconv (δ / 2) hδ2_pos)
      · intro n; exact zero_le _
      · intro n
        apply measure_mono
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        rw [Real.enorm_eq_ofReal_abs] at hω
        have h1 : δ ≤ |X n ω - Y ω| :=
          ENNReal.toReal_le_of_le_ofReal (abs_nonneg _) hω
        linarith
    exact (exists_seq_tendstoInMeasure_atTop_iff hX).mp hTIM
  ·
    intro hsub
    have hTIM : TendstoInMeasure μ X atTop Y :=
      (exists_seq_tendstoInMeasure_atTop_iff hX).mpr hsub
    rw [tendstoInMeasure_iff_enorm] at hTIM
    intro ε hε
    have hε_ennreal : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
    have hε_ne_top : ENNReal.ofReal ε ≠ ⊤ := ENNReal.ofReal_ne_top
    specialize hTIM (ENNReal.ofReal ε) hε_ennreal hε_ne_top
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hTIM
    · intro n; exact zero_le _
    · intro n
      apply measure_mono
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (le_of_lt hω)

/--
[convergence_in_probability_iff_subsequential_ae_convergence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/ConvProbSubseq.lean)
-/
@[path]
lemma convergence_in_probability_iff_subsequential_ae_convergence
  {m : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsFiniteMeasure μ]
  {X : ℕ → Ω → ℝ}
  {Y : Ω → ℝ}
-- given
  (hX : ∀ n, AEStronglyMeasurable (X n) μ) :
-- imply
  (∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ {ω | ε < |X n ω - Y ω|}) atTop (𝓝 0)) ↔ (∀ ns : ℕ → ℕ, StrictMono ns → ∃ ns' : ℕ → ℕ, StrictMono ns' ∧ ∀ᵐ ω ∂μ, Tendsto (fun k => X (ns (ns' k)) ω) atTop (𝓝 (Y ω))) :=
-- proof
  convergence_in_prob_iff_subseq_ae_real hX


-- created on 2026-10-23

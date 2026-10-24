import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TheoryOfProbability.code.StrongMarkovBMGoal98
open MeasureTheory ProbabilityTheory MeasurableSpace StrongMarkovBMGoal98
open scoped NNReal ENNReal


namespace StrongMarkovBMGoal98

/--
[bmExpectation_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/StrongMarkovBMGoal98.lean)
-/
@[path]
lemma bmExpectation_measurable
  {m : MeasurableSpace Ω}
  {d : ℕ}
  {m : MeasurableSpace Ω}
  {d : ℕ}
  {B : ℝ≥0 → Ω → Rd d}
  {ℱ : Filtration ℝ≥0 m}
  {P : Rd d → Measure Ω}
-- given
  (hBM : IsBrownianMotion B ℱ P)
  (Y : ℝ≥0 → (ℝ≥0 → Rd d) → ℝ)
  (hY_meas : Measurable (fun p : ℝ≥0 × (ℝ≥0 → Rd d) => Y p.1 p.2))
  (_hY_bdd : ∃ C : ℝ, ∀ t f, |Y t f| ≤ C) :
-- imply
  Measurable (fun p : ℝ≥0 × Rd d => bmExpectation B P Y p.1 p.2) := by
-- proof
  let κ : ProbabilityTheory.Kernel (ℝ≥0 × Rd d) Ω :=
    ⟨fun p => P p.2, hBM.measurable_P.comp measurable_snd⟩
  haveI : ProbabilityTheory.IsMarkovKernel κ :=
    ⟨fun p => hBM.isProbMeasure p.2⟩
  have hf_meas : Measurable (fun p : (ℝ≥0 × Rd d) × Ω =>
    Y p.1.1 (fun s => B s p.2)) := by
    let g : (ℝ≥0 × Rd d) × Ω → ℝ≥0 × (ℝ≥0 → Rd d) :=
      fun p => (p.1.1, fun s => B s p.2)
    have hg : Measurable g :=
      Measurable.prodMk measurable_fst.fst
        (measurable_pi_lambda _ fun s =>
          ((hBM.adapted s).mono (ℱ.le s) le_rfl).comp measurable_snd)
    show Measurable ((fun q : ℝ≥0 × (ℝ≥0 → Rd d) => Y q.1 q.2) ∘ g)
    exact hY_meas.comp hg
  have h_sm : StronglyMeasurable (fun p : ℝ≥0 × Rd d =>
    ∫ ω, Y p.1 (fun s => B s ω) ∂κ p) :=
    hf_meas.stronglyMeasurable.integral_kernel_prod_right'
  suffices h_eq : (fun p : ℝ≥0 × Rd d => ∫ ω, Y p.1 (fun s => B s ω) ∂κ p) =
    (fun p : ℝ≥0 × Rd d => bmExpectation B P Y p.1 p.2) by
    rw [← h_eq]; exact h_sm.measurable
  ext p
  rfl
/-- For an adapted process `B` (here a Brownian motion) and a stopping time `S`, the
random variable `ω ↦ B (S ω) ω` is measurable with respect to the stopping-time
σ-algebra `ℱ_S`. -/

end StrongMarkovBMGoal98


-- created on 2026-10-23

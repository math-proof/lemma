import Mathlib
import sympy.Basic
open MeasureTheory Filter Topology


namespace MathlibExt.Probability.LevyContinuityWanted

/--
[levy_continuity_of_charFun](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyContinuity.lean)
-/
@[path]
lemma levy_continuity_of_charFun
  {d : ℕ}
  {μn : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d))}
  {φ : EuclideanSpace ℝ (Fin d) → ℂ}
-- given
  (hφ : ∀ t, Tendsto (fun n => charFun (μn n : Measure _) t) atTop (nhds (φ t)))
  (hcont : ContinuousAt φ (0 : EuclideanSpace ℝ (Fin d))) :
-- imply
  ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      (∀ t, φ t = charFun (μ : Measure _) t) ∧
      Tendsto (fun n => μn n) atTop (nhds μ) := by
-- proof
  have h_tight : IsTightMeasureSet
    (Set.range fun n => ((μn n : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) :
      Measure (EuclideanSpace ℝ (Fin d)))) :=
    isTightMeasureSet_of_tendsto_charFun hcont hφ
  have hS : {x | ∃ μ ∈ Set.range μn,
    ((μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) :
      Measure (EuclideanSpace ℝ (Fin d))) = x} =
    Set.range fun n => ((μn n : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) :
      Measure (EuclideanSpace ℝ (Fin d))) := by
    ext x
    constructor
    · rintro ⟨μ, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨_, ⟨n, rfl⟩, rfl⟩
  have h_tight' : IsTightMeasureSet {x | ∃ μ ∈ Set.range μn,
    ((μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) :
      Measure (EuclideanSpace ℝ (Fin d))) = x} := by
    rwa [hS]
  have h_compact : IsCompact (closure (Set.range μn)) :=
    isCompact_closure_of_isTightMeasureSet h_tight'
  obtain ⟨μ', -, ϕ, hmono, hlim⟩ :=
    h_compact.isSeqCompact (fun n => subset_closure (Set.mem_range_self n))
  have heq : ∀ t, φ t = charFun
    (((μ' : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) :
      Measure (EuclideanSpace ℝ (Fin d)))) t := by
    intro t
    have h1 : Tendsto (fun n => charFun
      (((μn (ϕ n) : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) :
        Measure (EuclideanSpace ℝ (Fin d)))) t) atTop (𝓝 (φ t)) :=
      (hφ t).comp hmono.tendsto_atTop
    have h2 : Tendsto (fun n => charFun
      (((μn (ϕ n) : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) :
        Measure (EuclideanSpace ℝ (Fin d)))) t) atTop
      (𝓝 (charFun (((μ' : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) :
        Measure (EuclideanSpace ℝ (Fin d)))) t)) :=
      ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hlim t
    exact tendsto_nhds_unique h1 h2
  refine ⟨μ', heq, ?_⟩
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  rw [← heq t]
  exact hφ t

end MathlibExt.Probability.LevyContinuityWanted


-- created on 2026-10-20
-- updated on 2026-10-23

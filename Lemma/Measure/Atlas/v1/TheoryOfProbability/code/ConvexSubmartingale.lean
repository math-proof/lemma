import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory Filter


/--
[convex_comp_martingale_is_submartingale](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/ConvexSubmartingale.lean)
-/
@[path]
lemma convex_comp_martingale_is_submartingale
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0}
  {X : ℕ → Ω → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hmart : Martingale X ℱ μ)
  (hφ_convex : ConvexOn ℝ Set.univ φ)
  (hφ_int : ∀ n, Integrable (fun ω => φ (X n ω)) μ) :
-- imply
  Submartingale (fun n ω => φ (X n ω)) ℱ μ := by
-- proof
  have hφ_cont : Continuous φ :=
    continuousOn_univ.1 (hφ_convex.continuousOn isOpen_univ)
  refine ⟨?_, ?_, ?_⟩
  ·
    intro n
    exact hφ_cont.comp_stronglyMeasurable (hmart.stronglyMeasurable n)
  ·
    intro i j hij
    have hJensen : (φ ∘ μ[X j | ℱ i]) ≤ᵐ[μ] μ[φ ∘ (X j) | ℱ i] :=
      hφ_convex.map_condExp_le_of_finiteDimensional (ℱ.le i)
        (hmart.integrable j) (hφ_int j)
    have hcondexp : μ[X j | ℱ i] =ᵐ[μ] X i := hmart.condExp_ae_eq hij
    have hcomp : (fun ω => φ (X i ω)) =ᵐ[μ] (φ ∘ μ[X j | ℱ i]) := by
      filter_upwards [hcondexp] with ω hω
      simp [Function.comp, hω]
    exact hcomp.le.trans hJensen
  ·
    exact hφ_int


-- created on 2026-10-23

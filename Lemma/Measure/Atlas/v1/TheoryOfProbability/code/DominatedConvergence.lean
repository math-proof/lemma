import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.TheoryOfProbability.code.DominatedConvergence
open MeasureTheory Filter


/--
[dominated_convergence_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/DominatedConvergence.lean)
-/
@[path]
lemma dominated_convergence_theorem
  [NormedAddCommGroup G]
  [NormedSpace ℝ G]
  {m : MeasurableSpace α}
  {μ : Measure α}
  {F : ℕ → α → G}
  {f : α → G}
  {bound : α → ℝ}
-- given
  (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ)
  (h_bound_int : Integrable bound μ)
  (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
  (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (nhds (f a))) :
-- imply
  Tendsto (fun n => ∫ a, F n a ∂μ) atTop (nhds (∫ a, f a ∂μ)) :=
-- proof
  tendsto_integral_of_dominated_convergence bound hF_meas h_bound_int h_bound h_lim


-- created on 2026-10-23

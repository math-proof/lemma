/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/ODE/PicardIteration.lean -/


import Theorem.Analysis.ODE.PicardIteration
import Def.MathlibExtTest.Analysis.ODE.PicardIteration


namespace MetaMathlibExt

open MeasureTheory MathlibExt.Analysis.ODE.PicardIterationWanted

/-- Constant right-hand side: the proved Picard convergence theorem applies
to the iterates for `x' = 1`, `x 0 = 0`. -/
example : ∃ x : ℝ → ℝ, x 0 = (0 : ℝ) ∧ (∀ t, HasDerivAt x (1 : ℝ) t) ∧
    ∀ t, Filter.Tendsto (fun n => constU n t) Filter.atTop (nhds (x t)) := by
  obtain ⟨x, hx0, hx, hlim⟩ := picard_iterates_converge (E := ℝ)
    (fun _ _ => (1 : ℝ)) 0 0 0
    (by fun_prop) (fun t => by
      simpa using (LipschitzWith.const (1 : ℝ) (0 : ℝ)).lipschitzWith)
    constU constU_zero constU_step
  exact ⟨x, hx0, fun t => by simpa using hx t, hlim⟩

/-- The proved step-estimate theorem applies to the same iterates, without
any completeness hypothesis on the state space. -/
example (n : ℕ) (t : ℝ) :
    ‖constU (n + 1) t - constU n t‖ ≤
      1 * (0 : ℝ) ^ n * |t - 0| ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) :=
  picard_iterates_step_estimate (E := ℝ) (fun _ _ => (1 : ℝ)) 0 0 0
    (by fun_prop) (fun t => by
      simpa using (LipschitzWith.const (1 : ℝ) (0 : ℝ)).lipschitzWith)
    constU constU_zero constU_step
    1 (fun s => by norm_num) n t

end MetaMathlibExt

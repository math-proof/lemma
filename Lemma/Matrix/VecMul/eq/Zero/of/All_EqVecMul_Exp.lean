import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.TangentCone.Real
import Lemma.Matrix.HasDerivAtVecMul_Exp
open Matrix NormedSpace


@[path]
private lemma main
  [Fintype S] [DecidableEq S]
  {Q : Matrix S S ℝ}
  {μ : S → ℝ}
-- given
  (h₀ : ∀ t : ℝ, 0 ≤ t → μ ᵥ* exp (t • Q) = μ) :
-- imply
  μ ᵥ* Q = 0 := by
-- proof
  apply ((uniqueDiffOn_Ici (0 : ℝ)) 0 Set.self_mem_Ici).eq_deriv _
  · simpa using (Matrix.HasDerivAtVecMul_Exp Q μ 0).hasDerivWithinAt
  · apply (hasDerivWithinAt_const (0 : ℝ) (Set.Ici (0 : ℝ)) μ).congr (fun s hs => h₀ s hs) (h₀ 0 le_rfl)


-- created on 2026-09-26

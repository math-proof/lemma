import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.TangentCone.Real
import sympy.stats.generator_matrix
import sympy.Basic
import Lemma.NormedSpace.HasDerivAtVecMul_Exp
open Matrix NormedSpace


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {Q : Matrix S S ℝ}
  {μ : S → ℝ}
-- given
  (h₀ : ∀ t : ℝ, 0 ≤ t → μ ᵥ* exp (t • Q) = μ) :
-- imply
  μ ᵥ* Q = 0 := by
-- proof
  have h₁ : HasDerivWithinAt (fun s : ℝ => μ ᵥ* exp (s • Q)) (μ ᵥ* Q) (Set.Ici 0) 0 := by
    simpa using (NormedSpace.HasDerivAtVecMul_Exp Q μ 0).hasDerivWithinAt
  have h₂ : HasDerivWithinAt (fun s : ℝ => μ ᵥ* exp (s • Q)) 0 (Set.Ici 0) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) (Set.Ici (0 : ℝ)) μ).congr (fun s hs => h₀ s hs) (h₀ 0 le_rfl)
  exact ((uniqueDiffOn_Ici (0 : ℝ)) 0 Set.self_mem_Ici).eq_deriv _ h₁ h₂


-- created on 2026-09-26

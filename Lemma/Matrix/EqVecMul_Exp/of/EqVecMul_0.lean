import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Lemma.Matrix.HasDerivAtVecMul_Exp
open Matrix NormedSpace


@[path]
private lemma main
  [Fintype S] [DecidableEq S]
  {Q : Matrix S S ℝ}
  {μ : S → ℝ}
-- given
  (h₀ : μ ᵥ* Q = 0)
  (t : ℝ) :
-- imply
  μ ᵥ* exp (t • Q) = μ := by
-- proof
  have hd : ∀ s, HasDerivAt (fun s : ℝ => μ ᵥ* exp (s • Q)) 0 s := by
    intro s
    have h := Matrix.HasDerivAtVecMul_Exp Q μ s
    rwa [Matrix.vecMul_vecMul, ← (Commute.exp_right ((Commute.refl Q).smul_right s)).eq, ← Matrix.vecMul_vecMul, h₀, Matrix.zero_vecMul] at h
  simpa using is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0


-- created on 2026-09-26

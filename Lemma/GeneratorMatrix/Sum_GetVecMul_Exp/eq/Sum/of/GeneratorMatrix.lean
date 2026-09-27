import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Prod
import sympy.stats.generator_matrix
import sympy.Basic
import Lemma.NormedSpace.HasDerivAtVecMul_Exp
import Lemma.GeneratorMatrix.Sum_GetVecMul.eq.Zero.of.GeneratorMatrix
open Matrix NormedSpace


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {Q : Matrix S S ℝ}
-- given
  (h₀ : GeneratorMatrix Q)
  (ξ : S → ℝ)
  (t : ℝ) :
-- imply
  ∑ j, (ξ ᵥ* exp (t • Q)) j = ∑ j, ξ j := by
-- proof
  have hd : ∀ s, HasDerivAt (fun s : ℝ => ∑ j, (ξ ᵥ* exp (s • Q)) j) 0 s := by
    intro s
    exact (HasDerivAt.fun_sum (u := Finset.univ) fun j _ => hasDerivAt_pi.mp (NormedSpace.HasDerivAtVecMul_Exp Q ξ s) j).congr_deriv (GeneratorMatrix.Sum_GetVecMul.eq.Zero.of.GeneratorMatrix h₀ _)
  simpa using is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0


-- created on 2026-09-26

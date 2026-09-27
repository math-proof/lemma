import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Module.FiniteDimension
import sympy.stats.generator_matrix
import sympy.Basic
import Lemma.GeneratorMatrix.Sum_GetVecMul_Exp.eq.Sum.of.GeneratorMatrix
import Lemma.GeneratorMatrix.Exp.ge.Zero.of.Ge_0.GeneratorMatrix
open Matrix NormedSpace


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {Q : Matrix S S ℝ}
  {t : ℝ}
-- given
  (h₀ : GeneratorMatrix Q)
  (h₁ : 0 ≤ t) :
-- imply
  RowStochastic (exp (t • Q)) := by
-- proof
  refine ⟨fun s => ⟨fun j => GeneratorMatrix.Exp.ge.Zero.of.Ge_0.GeneratorMatrix h₀ h₁ s j, ?_⟩⟩
  simpa [Matrix.single_one_vecMul] using GeneratorMatrix.Sum_GetVecMul_Exp.eq.Sum.of.GeneratorMatrix h₀ (Pi.single s 1) t


-- created on 2026-09-26

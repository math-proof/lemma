import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Module.FiniteDimension
import sympy.stats.generator_matrix
import sympy.Basic
import Lemma.NormedSpace.Exp.ge.Zero.of.All_Ge_0
open Matrix NormedSpace


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {Q : Matrix S S ℝ}
  {t : ℝ}
-- given
  (h₀ : GeneratorMatrix Q)
  (h₁ : 0 ≤ t)
  (i j : S) :
-- imply
  0 ≤ exp (t • Q) i j := by
-- proof
  let c : ℝ := ∑ k, |Q k k|
  have hP : ∀ i j, 0 ≤ (t • (Q + c • 1)) i j := by
    intro i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul]
    apply mul_nonneg h₁
    if h : i = j then
      subst h
      have : |Q i i| ≤ c := Finset.single_le_sum (f := fun k => |Q k k|) (fun k _ => abs_nonneg _) (Finset.mem_univ i)
      simp
      linarith [neg_abs_le (Q i i)]
    else
      simp [h, h₀.offdiag_nonneg i j h]
  have hsplit : t • Q = t • (Q + c • 1) + (-(t * c)) • (1 : Matrix S S ℝ) := by
    rw [smul_add, smul_smul, add_assoc, ← add_smul]
    simp
  have hone : exp ((-(t * c)) • (1 : Matrix S S ℝ)) = Real.exp (-(t * c)) • (1 : Matrix S S ℝ) := by
    let _ : NormedRing (Matrix S S ℝ) := Matrix.linftyOpNormedRing
    let _ : NormedAlgebra ℝ (Matrix S S ℝ) := Matrix.linftyOpNormedAlgebra
    have h := algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := Matrix S S ℝ) (-(t * c))
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] at h
    exact h.symm
  rw [hsplit, Matrix.exp_add_of_commute _ _ ((Commute.one_right _).smul_right _), hone, mul_smul_one]
  exact mul_nonneg (Real.exp_pos _).le (NormedSpace.Exp.ge.Zero.of.All_Ge_0 hP i j)


-- created on 2026-09-26

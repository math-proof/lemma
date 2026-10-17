import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Data.Matrix.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Instances.Matrix
import sympy.Basic
open NormedSpace


@[path]
private lemma main
  {n : ℕ} {x : ℝ} :
-- imply
  HasSum (fun k : ℕ =>
      (-1 : ℝ) ^ k • (((2 * k + 1).factorial : ℝ)⁻¹ •
        ((x • (1 : Matrix (Fin n) (Fin n) ℝ)) ^ (2 * k + 1))))
    (Real.sin x • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
-- proof
  have hpow (k : ℕ) : (x • (1 : Matrix (Fin n) (Fin n) ℝ)) ^ k = (x ^ k) • 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
      simp [pow_succ, ih, smul_smul, mul_comm]
  have hs := Real.hasSum_sin x
  let L := ContinuousLinearMap.toSpanSingleton ℝ (1 : Matrix (Fin n) (Fin n) ℝ)
  convert L.hasSum hs using 1
  ·
    ext k
    rw [hpow]
    simp [L, ContinuousLinearMap.toSpanSingleton_apply, div_eq_mul_inv, smul_smul, Matrix.smul_apply]
    ring
  ·
    simp [L, ContinuousLinearMap.toSpanSingleton_apply]


-- created on 2026-10-11
-- updated on 2026-10-17

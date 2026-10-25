/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/ODE/LinearSystemFundamentalMatrix.lean -/


import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Def.Analysis.ODE.LinearSystemFundamentalMatrix.Part3
import Lemma.Real.ODE.LinearSystemFundamentalMatrix
open MeasureTheory

open MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted


-- The global scalar solver identifies exp(t²/2) as the unique solution of x' = t x.
example (x : ℝ → ℝ) (hx0 : x 0 = 1)
    (hx : ∀ t, HasDerivAt x (t * x t) t) :
    x = fun t ↦ Real.exp (t ^ 2 / 2) := by
  let B : ℝ → ℝ →L[ℝ] ℝ := fun t ↦ t • ContinuousLinearMap.id ℝ ℝ
  have hB : Continuous B := by fun_prop
  obtain ⟨y, _, hunique⟩ :=
    ODE.existsUnique_hasDerivAt_eq_continuousLinearMap B 0 1 hB
  have hcandidate (t : ℝ) : HasDerivAt (fun s : ℝ ↦ Real.exp (s ^ 2 / 2))
      (t * Real.exp (t ^ 2 / 2)) t := by
    have hquad : HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) t t := by
      convert (((hasDerivAt_id t).pow 2).div_const 2) using 1 <;>
        simp [id, mul_comm]
    simpa [mul_comm] using hquad.exp
  calc
    x = y := hunique x ⟨hx0, fun t ↦ by simpa [B] using hx t⟩
    _ = fun t ↦ Real.exp (t ^ 2 / 2) :=
      (hunique _ ⟨by norm_num, hcandidate⟩).symm

-- Jacobi's formula differentiates a nonzero diagonal determinant with trace three.
example (t : ℝ) :
    HasDerivAt
      (fun s ↦ (Matrix.diagonal ![Real.exp s, Real.exp (2 * s)]).det)
      (3 * Real.exp (3 * t)) t := by
  let Φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
    fun s ↦ Matrix.diagonal ![Real.exp s, Real.exp (2 * s)]
  let A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, 2]
  have hΦ : HasDerivAt Φ (A * Φ t) t := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases i <;> fin_cases j
    · simpa [Φ, A, Matrix.diagonal_mul] using Real.hasDerivAt_exp t
    · simpa [Φ, A, Matrix.diagonal_mul] using hasDerivAt_const t (0 : ℝ)
    · simpa [Φ, A, Matrix.diagonal_mul] using hasDerivAt_const t (0 : ℝ)
    · simpa [Φ, A, Matrix.diagonal_mul, mul_comm] using
        ((hasDerivAt_id t).const_mul 2).exp
  have ht : 3 * t = t + 2 * t := by ring
  have hdet := HasDerivAt.det_of_mul hΦ
  norm_num [Φ, A, ← Real.exp_add, ht] at hdet ⊢
  exact hdet

-- Liouville's formula integrates the nonconstant scalar trace t to t²/2.
example :
    ∃ Φ : ℝ → Matrix (Fin 1) (Fin 1) ℝ,
      Φ 0 = 1 ∧
      (∀ t, HasDerivAt Φ (!![t] * Φ t) t) ∧
      ∀ t, (Φ t).det = Real.exp (t ^ 2 / 2) := by
  let A : ℝ → Matrix (Fin 1) (Fin 1) ℝ := fun t ↦ !![t]
  have hA : Continuous A := by fun_prop
  obtain ⟨Φ, hΦ0, hΦ, _, _⟩ := fundamental_matrix_linear_system A 0 hA
  refine ⟨Φ, hΦ0, ?_, ?_⟩
  · intro t
    simpa [A] using hΦ t
  · intro t
    have hdet := fundamental_matrix_liouville_det A 0 hA Φ hΦ0 hΦ t
    simpa [A, hΦ0, integral_id] using hdet

-- Uniqueness identifies the nilpotent system's second-column solution explicitly.
example (t₀ : ℝ) :
    ∃ Φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ,
      Φ t₀ = 1 ∧
      (∀ t, HasDerivAt Φ (!![0, 1; 0, 0] * Φ t) t) ∧
      ∀ t, (Φ t).mulVec ![0, 1] = ![t - t₀, 1] := by
  let A : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun _ ↦ !![0, 1; 0, 0]
  have hA : Continuous A := continuous_const
  obtain ⟨Φ, hΦ0, hΦ, _, hsol⟩ := fundamental_matrix_linear_system A t₀ hA
  obtain ⟨x, _, _, hxΦ, hunique⟩ := hsol ![0, 1]
  let y : ℝ → Fin 2 → ℝ := fun t ↦ ![t - t₀, 1]
  have hy0 : y t₀ = ![0, 1] := by simp [y]
  have hy (t : ℝ) : HasDerivAt y ((A t).mulVec (y t)) t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [A, y, Matrix.mulVec, Fin.sum_univ_two] using
        (hasDerivAt_id t).sub_const t₀
    · simpa [A, y, Matrix.mulVec, Fin.sum_univ_two] using
        hasDerivAt_const t (1 : ℝ)
  have hyx : y = x := hunique y hy0 hy
  refine ⟨Φ, hΦ0, ?_, ?_⟩
  · intro t
    simpa [A] using hΦ t
  · intro t
    calc
      (Φ t).mulVec ![0, 1] = x t := (hxΦ t).symm
      _ = y t := (congrFun hyx t).symm
      _ = ![t - t₀, 1] := rfl

-- Invertibility makes evaluation at any time injective on initial values.
example {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (t₀ t : ℝ)
    (hA : Continuous A) (x y : ℝ → Fin n → ℝ)
    (hx : ∀ s, HasDerivAt x ((A s).mulVec (x s)) s)
    (hy : ∀ s, HasDerivAt y ((A s).mulVec (y s)) s)
    (hxy : x t = y t) : x t₀ = y t₀ := by
  obtain ⟨Φ, _, _, hunit, hsol⟩ := fundamental_matrix_linear_system A t₀ hA
  obtain ⟨x', _, _, hxΦ, hxunique⟩ := hsol (x t₀)
  obtain ⟨y', _, _, hyΦ, hyunique⟩ := hsol (y t₀)
  have hxx' : x = x' := hxunique x rfl hx
  have hyy' : y = y' := hyunique y rfl hy
  have hxt : x t = (Φ t).mulVec (x t₀) := by
    exact (congrFun hxx' t).trans (hxΦ t)
  have hyt : y t = (Φ t).mulVec (y t₀) := by
    exact (congrFun hyy' t).trans (hyΦ t)
  have hdet : IsUnit (Φ t).det := hunit t
  apply Matrix.mulVec_injective_of_det_ne_zero hdet.ne_zero
  exact hxt.symm.trans (hxy.trans hyt)


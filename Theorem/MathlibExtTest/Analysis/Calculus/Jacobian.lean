/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Calculus/Jacobian.lean -/


import Theorem.Analysis.Calculus.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension
open MetaMathlibExt
open scoped Matrix


-- Composing two matrix actions multiplies their Jacobian matrices.
example {m n p : ℕ} (M : Matrix (Fin p) (Fin n) ℝ)
    (N : Matrix (Fin n) (Fin m) ℝ) (x : Fin m → ℝ) :
    jacobianMatrix (fun y => M *ᵥ (N *ᵥ y)) x = M * N := by
  let LM : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)
  let LN : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin N)
  have hN : DifferentiableAt ℝ (fun y => N *ᵥ y) x := by
    change DifferentiableAt ℝ (fun y => LN y) x
    exact LN.differentiableAt
  have hM : DifferentiableAt ℝ (fun y => M *ᵥ y) (N *ᵥ x) := by
    change DifferentiableAt ℝ (fun y => LM y) (N *ᵥ x)
    exact LM.differentiableAt
  calc
    jacobianMatrix (fun y => M *ᵥ (N *ᵥ y)) x =
        jacobianMatrix (fun y => M *ᵥ y) (N *ᵥ x) *
          jacobianMatrix (fun y => N *ᵥ y) x := by
      simpa only [Function.comp_def] using
        jacobianMatrix_comp (fun y => N *ᵥ y) (fun y => M *ᵥ y) x hN hM
    _ = M * N := by
      rw [jacobianMatrix_fun_mulVec M (N *ᵥ x), jacobianMatrix_fun_mulVec N x]

-- A nonlinear polynomial map has the expected point-dependent Jacobian.
example (x : Fin 2 → ℝ) :
    jacobianMatrix (fun y : Fin 2 → ℝ => ![y 0 * y 1, y 0 + y 1]) x =
      !![x 1, x 0; 1, 1] := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) x
  have hmul := h0.mul h1
  have hadd := h0.add h1
  have hmul_diff : DifferentiableAt ℝ (fun y : Fin 2 → ℝ => y 0 * y 1) x := by
    convert hmul.differentiableAt using 1
  have hadd_diff : DifferentiableAt ℝ (fun y : Fin 2 → ℝ => y 0 + y 1) x := by
    convert hadd.differentiableAt using 1
  have hmul_fderiv : fderiv ℝ (fun y : Fin 2 → ℝ => y 0 * y 1) x =
      x 0 • ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2) +
        x 1 • ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2) := by
    convert hmul.fderiv using 1
  have hadd_fderiv : fderiv ℝ (fun y : Fin 2 → ℝ => y 0 + y 1) x =
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2) +
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (1 : Fin 2) := by
    convert hadd.fderiv using 1
  have hf : DifferentiableAt ℝ
      (fun y : Fin 2 → ℝ => ![y 0 * y 1, y 0 + y 1]) x := by
    rw [differentiableAt_pi]
    intro i
    fin_cases i
    · simpa using hmul_diff
    · simpa using hadd_diff
  ext i j
  rw [jacobianMatrix_apply_of_differentiableAt _ _ hf]
  rw [fderiv_pi (differentiableAt_pi.mp hf)]
  simp only [ContinuousLinearMap.coe_pi']
  fin_cases i <;> fin_cases j <;> simp [hmul_fderiv, hadd_fderiv]


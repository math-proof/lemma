import Def.Data.Vector.Functions
import Instance.Analysis.InnerProductSpace.EuclideanVec
import Instance.LinearAlgebra.Matrix.EuclideanVec
import Lemma.Real.Grad.eq.Stack
import Lemma.Real.Grad.Softmax.eq.Mul.Softmax
import Syntax.Analysis.Calculus.Deriv.Operators
import Syntax.Analysis.Calculus.Gradient.Operators
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
open Real
open scoped Matrix


/--
The Jacobian of softmax with respect to the input vector `x`. The gradient of
output component `j` is its softmax weight times the difference between the
gradient of logit `j` and the softmax-weighted sum of the logit gradients.
-/
@[path]
private lemma main
  {n : ℕ}
  {F : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)}
  {x : EuclideanSpace ℝ (Fin n)}
-- given
  (h₀ : DifferentiableAt ℝ F x) :
-- imply
  ∇[x] (F x).softmax =
    (F x).softmax •
      ((∇[x] F x) - (F x).softmax ᵥ* (∇[x] F x : Matrix (Fin n) (Fin n) ℝ)) := by
-- proof
  have hM : (∇[x] F x : Matrix (Fin n) (Fin n) ℝ) =
    Matrix.of (fun i : Fin n => WithLp.ofLp (∇[x] F x i)) := rfl
  rw [hM]
  have h := differentiableAt_pi.mp h₀
  funext j
  ext k
  have hR :
    ((F x).softmax •
        ((∇[x] F x) - (F x).softmax ᵥ* Matrix.of (fun i : Fin n => WithLp.ofLp (∇[x] F x i)))) j =
      (F x).softmax j •
        ((∇[x] F x j) -
          WithLp.toLp 2 ((F x).softmax ᵥ* Matrix.of (fun i : Fin n => WithLp.ofLp (∇[x] F x i)))) :=
    rfl
  rw [hR]
  have hexp (z : ℝ) : Exp.exp z = z.exp := rfl
  simp only [Function.softmax, hexp, PiLp.smul_apply, PiLp.sub_apply,
    Matrix.vecMul_apply_eq_sum, Matrix.of_apply, smul_eq_mul, Grad.eq.Stack]
  let S := fun y : EuclideanSpace ℝ (Fin n) => ∑ i : Fin n, (F y i).exp
  have hS : 0 < S x := Finset.sum_pos (fun i _ => Real.exp_pos _) ⟨j, Finset.mem_univ j⟩
  have hden : HasFDerivAt S
    (∑ i : Fin n, (F x i).exp • fderiv ℝ (fun y => F y i) x) x :=
    HasFDerivAt.fun_sum fun i _ => (h i).hasFDerivAt.exp
  have hq := (h j).hasFDerivAt.exp.fun_mul
    ((hasDerivAt_inv hS.ne').comp_hasFDerivAt x hden)
  change fderiv ℝ (fun y => (F y j).exp * (S y)⁻¹) x _ = _
  simp only [Function.comp_apply] at hq
  rw [hq.fderiv]
  simp only [add_apply, smul_apply,
    sum_apply, smul_eq_mul]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  change _ = (F x j).exp *
    (_ - (∑ i : Fin n, (F x i).exp * fderiv ℝ (fun y => F y i) x (EuclideanSpace.single k 1)) / S x) / S x
  field_simp [hS.ne']
  ring

/--
The gradient of softmax with respect to a scalar input. The gradient of
output component `j` is its softmax weight times the difference between the
derivative of logit `j` and the softmax-weighted sum of the logit derivatives.
-/
@[path]
private lemma scalar
  {n : ℕ}
  {F : ℝ → (Fin n → ℝ)}
  {x : ℝ}
-- given
  (h₀ : DifferentiableAt ℝ F x) :
-- imply
  (fun j => ∂[x] (F x).softmax j) =
    (F x).softmax • ((fun i => ∂[x] F x i) - (∑ i : Fin n, (F x).softmax i * ∂[x] F x i) • 1) := by
-- proof
  have h := differentiableAt_pi.mp h₀
  have hexp (z : ℝ) : Exp.exp z = z.exp := rfl
  funext j
  simp only [hexp, Function.softmax, Pi.mul_apply, Pi.sub_apply, Pi.smul_apply,
    Pi.one_apply, smul_eq_mul, mul_one]
  exact stack (F := fun i y => F y i) h j


-- created on 2023-03-18
-- updated on 2026-11-20

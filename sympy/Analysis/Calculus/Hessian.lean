/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Data.Matrix.Basic

import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Hessian matrices

This file relates coordinatewise Hessian matrices to second Fréchet derivatives, proves their
symmetry for twice continuously differentiable functions, and proves positive semidefiniteness at
local minima.
-/

open scoped BigOperators

open Set

namespace Real.Calculus.Hessian

/-- Hessian matrix of `f` at `x` as an `n × n` real matrix. -/
noncomputable def hessianMatrix {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => deriv (fun s : ℝ => deriv (fun t : ℝ =>
    f (x + s • Pi.single i (1 : ℝ) + t • Pi.single j (1 : ℝ))) 0) 0

/-- Characteristic spec: the `(i, j)` entry is the iterated second partial
derivative along the `i`-th then `j`-th coordinate axes. -/
theorem hessianMatrix_apply {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (i j : Fin n) :
    hessianMatrix f x i j =
      deriv (fun s : ℝ => deriv (fun t : ℝ =>
        f (x + s • Pi.single i (1 : ℝ) + t • Pi.single j (1 : ℝ))) 0) 0 := rfl

private theorem hessian_deriv_line {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (hf : Differentiable ℝ f)
    (x v : E) (t : ℝ) :
    deriv (fun s : ℝ => f (x + s • v)) t = fderiv ℝ f (x + t • v) v := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id (𝕜 := ℝ) t).smul_const v).const_add x
  simpa [Function.comp_def] using
    ((hf (x + t • v)).hasFDerivAt.comp_hasDerivAt t hline).deriv

private theorem hessian_deriv_fderiv_line {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F)
    (hf : ContDiff ℝ 2 f) (x v w : E) :
    deriv (fun t : ℝ => fderiv ℝ f (x + t • v) w) 0 =
      fderiv ℝ (fderiv ℝ f) x v w := by
  have hfderiv : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have heval : Differentiable ℝ (fun y => fderiv ℝ f y w) :=
    hfderiv.clm_apply (differentiable_const w)
  rw [hessian_deriv_line _ heval]
  simp only [zero_smul, add_zero]
  have happ := congrArg (fun L : E →L[ℝ] F => L v)
    (fderiv_clm_apply (c := fderiv ℝ f) (u := fun _ => w)
      (hfderiv x) (differentiableAt_const w))
  simpa using happ

private theorem hessian_deriv_deriv_line {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) (hf : ContDiff ℝ 2 f) (x v : E) :
    deriv (deriv (fun t : ℝ => f (x + t • v))) 0 =
      fderiv ℝ (fderiv ℝ f) x v v := by
  have hfdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfirst : deriv (fun t : ℝ => f (x + t • v)) =
      fun t => fderiv ℝ f (x + t • v) v := by
    funext t
    exact hessian_deriv_line f hfdiff x v t
  rw [hfirst]
  exact hessian_deriv_fderiv_line f hf x v v

private theorem hessian_clm_apply_self_eq_sum {n : ℕ}
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    B v v = ∑ i, ∑ j, v i * B (Pi.single i 1) (Pi.single j 1) * v j := by
  classical
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_comm, mul_left_comm]

/-- The entries of the Hessian matrix are evaluations of the second Fréchet derivative on the
standard basis. -/
theorem hessianMatrix_eq_fderiv_fderiv {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ 2 f) (x : Fin n → ℝ) (i j : Fin n) :
    hessianMatrix f x i j =
      fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) := by
  rw [hessianMatrix_apply]
  have hfdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  simp_rw [hessian_deriv_line f hfdiff]
  simp only [zero_smul, add_zero]
  exact hessian_deriv_fderiv_line f hf x (Pi.single i 1) (Pi.single j 1)

/-- The Hessian of a `C^2` function is symmetric. -/
theorem hessianMatrix_symmetric {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ 2 f) (x : Fin n → ℝ) :
    (hessianMatrix f x).transpose = hessianMatrix f x := by
  ext i j
  rw [Matrix.transpose_apply, hessianMatrix_eq_fderiv_fderiv f hf x j i,
    hessianMatrix_eq_fderiv_fderiv f hf x i j]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

/-- At a local minimum of a twice continuously differentiable real function, the second
derivative is nonnegative. This is the necessary direction of the one-variable second derivative
test. -/
theorem _root_.IsLocalMin.deriv_deriv_nonneg {g : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin g x) (hg : ContDiff ℝ 2 g) : 0 ≤ deriv (deriv g) x := by
  by_contra h
  have hneg : deriv (deriv g) x < 0 := lt_of_not_ge h
  have hg' : ContDiff ℝ 1 (deriv g) := by
    simpa using (hg.deriv' : ContDiff ℝ 1 (deriv g))
  have hzero : ContinuousAt (fun _ : ℝ => (0 : ℝ)) x := by fun_prop
  have hsecond : ∀ᶠ y in nhds x, deriv (deriv g) y < 0 :=
    (hg'.continuous_deriv (by norm_num)).continuousAt.eventually_lt hzero hneg
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hmin.and hsecond)
  have hzball : x + r / 2 ∈ Metric.ball x r := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos]
    · linarith
    · linarith
  have hxz : x < x + r / 2 := by linarith
  have hxmem : x ∈ Icc x (x + r / 2) := ⟨le_rfl, hxz.le⟩
  have hzmem : x + r / 2 ∈ Icc x (x + r / 2) := ⟨hxz.le, le_rfl⟩
  have hderivAnti : StrictAntiOn (deriv g) (Icc x (x + r / 2)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc x (x + r / 2))
      (hg.continuous_deriv (by norm_num)).continuousOn
    intro y hy
    rw [interior_Icc] at hy
    rcases hy with ⟨hxy, hyz⟩
    apply (hball ?_).2
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hxy)]
    linarith
  have hgAnti : StrictAntiOn g (Icc x (x + r / 2)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc x (x + r / 2))
      (hg.differentiable (by norm_num)).continuous.continuousOn
    intro y hy
    rw [interior_Icc] at hy
    rcases hy with ⟨hxy, hyz⟩
    have hymem : y ∈ Icc x (x + r / 2) := ⟨hxy.le, hyz.le⟩
    simpa [hmin.deriv_eq_zero] using hderivAnti hxmem hymem hxy
  exact (not_lt_of_ge (hball hzball).1) (hgAnti hxmem hzmem hxz)

/-- Second-derivative test, necessary direction: at a local minimizer of a
`C^2` function the Hessian quadratic form is nonnegative. -/
theorem isLocalMin_hessian_quadratic_nonneg {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ 2 f) (x : Fin n → ℝ) (hmin : IsLocalMin f x)
    (v : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, v i * hessianMatrix f x i j * v j := by
  let g : ℝ → ℝ := fun t => f (x + t • v)
  have hg : ContDiff ℝ 2 g := by
    dsimp [g]
    fun_prop
  have hline : ContinuousAt (fun t : ℝ => x + t • v) 0 := by fun_prop
  have hgmin : IsLocalMin g 0 := by
    have hmin0 : IsLocalMin f (x + (0 : ℝ) • v) := by simpa using hmin
    simpa [g, Function.comp_def] using
      hmin0.comp_continuous (g := fun t : ℝ => x + t • v) hline
  have hnonneg := hgmin.deriv_deriv_nonneg hg
  change 0 ≤ deriv (deriv (fun t : ℝ => f (x + t • v))) 0 at hnonneg
  rw [hessian_deriv_deriv_line f hf x v, hessian_clm_apply_self_eq_sum] at hnonneg
  simpa only [hessianMatrix_eq_fderiv_fderiv f hf x] using hnonneg

end Real.Calculus.Hessian

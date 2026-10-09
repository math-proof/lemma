import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f : EuclideanSpace ℝ (Fin n) → ℝ}
  {x : EuclideanSpace ℝ (Fin n)}
-- given
  (hne : gradient f x ≠ 0) :
-- imply
  deriv (fun η : ℝ => f (x - η • gradient f x)) 0 < 0 := by
-- proof
  have hd : DifferentiableAt ℝ f x := by
    by_contra h
    rw [gradient_eq_zero_of_not_differentiableAt h] at hne
    exact hne rfl
  set G := gradient f x with hG
  have hpos : 0 < ‖G‖ ^ 2 := by
    apply pow_pos
    exact norm_pos_iff.mpr hne
  have hinner : HasDerivAt (fun t : ℝ => x - t • G) (-G) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x - t • G) ((0 : EuclideanSpace ℝ (Fin n)) - (1 : ℝ) • G) 0 :=
      HasDerivAt.sub (hasDerivAt_const (0 : ℝ) x) ((hasDerivAt_id (0 : ℝ)).smul_const G)
    simpa using h1
  have hcomp : HasDerivAt (fun t : ℝ => f (x - t • G)) ((fderiv ℝ f x) (-G)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hd.hasFDerivAt hinner (by simp)
  have hval : (fderiv ℝ f x) (-G) = -‖G‖ ^ 2 := by
    rw [map_neg, ← inner_gradient_left, ← hG, real_inner_self_eq_norm_sq]
  rw [HasDerivAt.deriv hcomp, hval]
  linarith


-- created on 2026-10-09

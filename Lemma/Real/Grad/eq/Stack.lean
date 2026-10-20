import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import sympy.Basic
open InnerProductSpace


@[path]
private lemma main
  {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)} {i : Fin n} :
-- imply
  gradient f x i = fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)) := by
-- proof
  have hinner := toDual_symm_apply (𝕜 := ℝ)
    (x := EuclideanSpace.single i (1 : ℝ)) (y := fderiv ℝ f x)
  unfold gradient
  simp only [EuclideanSpace.inner_single_right, one_mul] at hinner
  exact hinner


-- created on 2021-12-25
-- updated on 2026-10-17

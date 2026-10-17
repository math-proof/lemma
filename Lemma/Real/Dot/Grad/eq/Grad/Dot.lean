import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import sympy.Basic
open InnerProductSpace


@[path]
private lemma main
  {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
  {a x v : EuclideanSpace ℝ (Fin n)}
  (h₀ : DifferentiableAt ℝ g x) :
-- imply
  fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => ⟪a, g y⟫_ℝ) x v =
    ⟪a, fderiv ℝ g x v⟫_ℝ := by
-- proof
  have hcomp := ((innerSL ℝ a).hasFDerivAt.comp x h₀.hasFDerivAt)
  have hfun : (fun y : EuclideanSpace ℝ (Fin n) => ⟪a, g y⟫_ℝ) = ⇑(innerSL ℝ a) ∘ g := by
    funext y
    rw [Function.comp_apply, innerSL_apply_apply]
  rw [hfun, hcomp.fderiv]
  simp [ContinuousLinearMap.comp_apply, innerSL_apply_apply]


-- created on 2026-10-11
-- updated on 2026-10-17

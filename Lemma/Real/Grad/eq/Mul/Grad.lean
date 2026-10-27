import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ} {φ : ℝ → ℝ} {x : Fin n → ℝ} {i j : Fin n}
  (h₀ : DifferentiableAt ℝ φ (x j)) :
-- imply
  fderiv ℝ (fun y : Fin n → ℝ => φ (y j)) x (Pi.single i (1 : ℝ)) =
    if i = j then deriv φ (x j) else 0 := by
-- proof
  have happ : HasFDerivAt (fun y : Fin n → ℝ => y j)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j) x :=
    hasFDerivAt_apply j x
  have hcomp := h₀.hasFDerivAt.comp x happ
  have hfun : (fun y : Fin n → ℝ => φ (y j)) = φ ∘ fun y => y j := rfl
  rw [hfun, hcomp.fderiv]
  if h : i = j then
    simp [h, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  else
    simp [h, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]


-- created on 2023-03-18
-- updated on 2026-10-26

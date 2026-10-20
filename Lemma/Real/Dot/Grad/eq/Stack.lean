import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import sympy.Basic


@[path]
private lemma main
  {n : ℕ} {φ : ℝ → ℝ} {x : Fin n → ℝ}
  (h₀ : ∀ i, DifferentiableAt ℝ φ (x i)) :
-- imply
  fderiv ℝ (fun y : Fin n → ℝ => fun i => φ (y i)) x (fun _ => (1 : ℝ)) =
    fun i => deriv φ (x i) := by
-- proof
  have hpi := hasFDerivAt_pi.2 fun i =>
    (h₀ i).hasFDerivAt.comp x (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin n => ℝ) i x)
  rw [show (fun y : Fin n → ℝ => fun i => φ (y i)) =
      fun y i => (φ ∘ fun z => z i) y by rfl, hpi.fderiv]
  ext i
  simp [ContinuousLinearMap.proj_apply]


-- created on 2023-03-19
-- updated on 2026-10-17

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ} {φ : ℝ → ℝ} {x v : Fin n → ℝ}
  (h₀ : ∀ i, DifferentiableAt ℝ φ (x i)) :
-- imply
  fderiv ℝ (fun y : Fin n → ℝ => fun i => φ (y i)) x v =
    fun i => deriv φ (x i) * v i := by
-- proof
  have hpi := hasFDerivAt_pi.2 fun i =>
    (h₀ i).hasFDerivAt.comp x (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin n => ℝ) i x)
  have hfun : (fun y : Fin n → ℝ => fun i => φ (y i)) =
      fun y i => (φ ∘ fun z => z i) y := rfl
  rw [hfun, hpi.fderiv]
  ext i
  simp [ContinuousLinearMap.proj_apply]
  ring


-- created on 2023-03-18
-- updated on 2026-10-26

import Mathlib.Analysis.Normed.Lp.PiLp
import sympy.Basic


@[main]
private lemma main
  [Fintype α]
  {f : α → ℝ} :
-- imply
  ‖(WithLp.toLp ⊤ f : PiLp ⊤ fun _ : α => ℝ)‖ = ‖f‖ := by
-- proof
  rw [PiLp.norm_eq_ciSup]
  refine le_antisymm ?_ ?_
  · if hα : Nonempty α then
      exact ciSup_le fun i => by simpa using norm_le_pi_norm f i
    else
      simp [not_nonempty_iff.1 hα]
  · refine pi_norm_le_iff_of_nonneg (Real.iSup_nonneg fun i => norm_nonneg _) |>.2 fun i => ?_
    exact le_ciSup (f := fun i => ‖(WithLp.toLp ⊤ f : PiLp ⊤ fun _ : α => ℝ).ofLp i‖) (Set.finite_range _).bddAbove i


-- created on 2026-09-26
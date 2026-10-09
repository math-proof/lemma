import Mathlib
import sympy.Basic
import sympy.Analysis.Convex.KarushKuhnTucker

open Convex.KarushKuhnTucker

/--
[karush_kuhn_tucker_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/KarushKuhnTucker.lean)
-/
@[path]
private lemma karush_kuhn_tucker_inequality_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {m : ℕ} {f : E → ℝ} {g : Fin m → E → ℝ} {x : E}
  (hf_diff : DifferentiableAt ℝ f x)
  (hg_diff : ∀ i, DifferentiableAt ℝ (g i) x)
  (hfeas : ∀ i, g i x ≤ 0)
  (hmin : IsLocalMinOn f {y | ∀ i, g i y ≤ 0} x)
  (hLICQ : LinearIndependent ℝ
    (fun i : {i : Fin m // g i x = 0} => fderiv ℝ (g i.val) x)) :
-- imply
  ∃ lam : Fin m → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * g i x = 0) ∧
    fderiv ℝ f x + ∑ i : Fin m, lam i • fderiv ℝ (g i) x = 0 := by
-- proof
  apply karush_kuhn_tucker_inequality hf_diff hg_diff hfeas hmin hLICQ

-- created on 2026-10-09

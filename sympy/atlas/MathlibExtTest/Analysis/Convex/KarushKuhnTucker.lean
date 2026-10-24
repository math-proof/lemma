/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Convex/KarushKuhnTucker.lean -/

/-
Author: @toskua, Avocado
-/

import sympy.atlas.Analysis.Convex.KarushKuhnTucker

/-!
# Tests for the inequality-only KKT conditions

Focused API examples for
`MathlibExt.Analysis.Convex.KarushKuhnTucker.karush_kuhn_tucker_inequality`:
projections onto multiplier nonnegativity, complementarity, and stationarity,
plus a one-dimensional specialization over `ℝ`.
-/


open MathlibExt.Analysis.Convex.KarushKuhnTucker

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {m : ℕ} {f : E → ℝ} {g : Fin m → E → ℝ} {x : E}

/-- The KKT multipliers are nonnegative. -/
example
    (hf_diff : DifferentiableAt ℝ f x)
    (hg_diff : ∀ i, DifferentiableAt ℝ (g i) x)
    (hfeas : ∀ i, g i x ≤ 0)
    (hmin : IsLocalMinOn f {y | ∀ i, g i y ≤ 0} x)
    (hLICQ : LinearIndependent ℝ
      (fun i : {i : Fin m // g i x = 0} => fderiv ℝ (g i.val) x)) :
    ∃ lam : Fin m → ℝ, ∀ i, 0 ≤ lam i := by
  obtain ⟨lam, hnn, -, -⟩ :=
    karush_kuhn_tucker_inequality hf_diff hg_diff hfeas hmin hLICQ
  exact ⟨lam, hnn⟩

/-- The KKT multipliers satisfy complementarity. -/
example
    (hf_diff : DifferentiableAt ℝ f x)
    (hg_diff : ∀ i, DifferentiableAt ℝ (g i) x)
    (hfeas : ∀ i, g i x ≤ 0)
    (hmin : IsLocalMinOn f {y | ∀ i, g i y ≤ 0} x)
    (hLICQ : LinearIndependent ℝ
      (fun i : {i : Fin m // g i x = 0} => fderiv ℝ (g i.val) x)) :
    ∃ lam : Fin m → ℝ, ∀ i, lam i * g i x = 0 := by
  obtain ⟨lam, -, hcomp, -⟩ :=
    karush_kuhn_tucker_inequality hf_diff hg_diff hfeas hmin hLICQ
  exact ⟨lam, hcomp⟩

/-- The KKT stationarity equation holds. -/
example
    (hf_diff : DifferentiableAt ℝ f x)
    (hg_diff : ∀ i, DifferentiableAt ℝ (g i) x)
    (hfeas : ∀ i, g i x ≤ 0)
    (hmin : IsLocalMinOn f {y | ∀ i, g i y ≤ 0} x)
    (hLICQ : LinearIndependent ℝ
      (fun i : {i : Fin m // g i x = 0} => fderiv ℝ (g i.val) x)) :
    ∃ lam : Fin m → ℝ,
      fderiv ℝ f x + ∑ i : Fin m, lam i • fderiv ℝ (g i) x = 0 := by
  obtain ⟨lam, -, -, hstat⟩ :=
    karush_kuhn_tucker_inequality hf_diff hg_diff hfeas hmin hLICQ
  exact ⟨lam, hstat⟩

/-- Multipliers vanish on inactive constraints. -/
example
    (hf_diff : DifferentiableAt ℝ f x)
    (hg_diff : ∀ i, DifferentiableAt ℝ (g i) x)
    (hfeas : ∀ i, g i x ≤ 0)
    (hmin : IsLocalMinOn f {y | ∀ i, g i y ≤ 0} x)
    (hLICQ : LinearIndependent ℝ
      (fun i : {i : Fin m // g i x = 0} => fderiv ℝ (g i.val) x))
    (j : Fin m) (hj : g j x < 0) :
    ∃ lam : Fin m → ℝ, lam j = 0 := by
  obtain ⟨lam, -, hcomp, -⟩ :=
    karush_kuhn_tucker_inequality hf_diff hg_diff hfeas hmin hLICQ
  refine ⟨lam, ?_⟩
  have hj0 := hcomp j
  have hne : g j x ≠ 0 := ne_of_lt hj
  exact (mul_eq_zero.mp hj0).resolve_right hne

/-- One-dimensional specialization over `ℝ`. -/
example
    {φ : ℝ → ℝ} {ψ : Fin m → ℝ → ℝ} {a : ℝ}
    (hφ : DifferentiableAt ℝ φ a)
    (hψ : ∀ i, DifferentiableAt ℝ (ψ i) a)
    (hfeas : ∀ i, ψ i a ≤ 0)
    (hmin : IsLocalMinOn φ {y | ∀ i, ψ i y ≤ 0} a)
    (hLICQ : LinearIndependent ℝ
      (fun i : {i : Fin m // ψ i a = 0} => fderiv ℝ (ψ i.val) a)) :
    ∃ lam : Fin m → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * ψ i a = 0) ∧
      fderiv ℝ φ a + ∑ i : Fin m, lam i • fderiv ℝ (ψ i) a = 0 :=
  karush_kuhn_tucker_inequality hφ hψ hfeas hmin hLICQ

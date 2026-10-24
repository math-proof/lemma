/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/LaplaceTransform/Basic.lean -/


import sympy.atlas.Analysis.LaplaceTransform.Basic

/-!
# Laplace transform API checks

Anonymous checks that the Stage 1 Laplace API unfolds to the stated predicates and
integrals. No convergence claim is proved here.
-/


open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

-- `LaplaceConvergent` is definitionally the stated `IntegrableOn` predicate.
example (f : ℝ → E) (s : ℂ) :
    LaplaceConvergent f s =
      IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • f t) (Set.Ioi 0) :=
  rfl

-- `laplace` is definitionally the stated one-sided integral.
example (f : ℝ → E) (s : ℂ) :
    laplace f s = ∫ t : ℝ in Set.Ioi 0, Complex.exp (-s * (t : ℂ)) • f t :=
  rfl

-- Convergence packages with the transform value.
example (f : ℝ → E) (s : ℂ) (hf : LaplaceConvergent f s) :
    HasLaplace f s (laplace f s) :=
  ⟨hf, rfl⟩

-- Real-valued functions coerce to the ATLAS integrand with `*` over `Set.Ioi 0`.
example (h : ℝ → ℝ) (s : ℂ) :
    LaplaceConvergent (fun t => (h t : ℂ)) s =
      IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * (h t : ℂ))
        (Set.Ioi 0) := by
  simp only [LaplaceConvergent, smul_eq_mul]

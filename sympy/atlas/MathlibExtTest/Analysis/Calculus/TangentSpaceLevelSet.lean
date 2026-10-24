/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Calculus/TangentSpaceLevelSet.lean -/


import sympy.atlas.Analysis.Calculus.TangentSpaceLevelSet
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open Filter
open scoped Topology

open MetaMathlibExt

-- The standard unit-circle parametrization supplies its vertical tangent at `(1, 0)`.
example :
    fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) (1, 0) (0, 1) = 0 := by
  apply levelSet_tangent_vel_of_curve (c := 1)
      (γ := fun t : ℝ => (Real.cos t, Real.sin t))
  · exact (differentiableAt_fst.pow 2).add (differentiableAt_snd.pow 2)
  · simp
  · simpa using (Real.hasDerivAt_cos 0).prodMk (Real.hasDerivAt_sin 0)
  · exact Real.cos_sq_add_sin_sq

-- The first projection realizes vertical vectors by both local and global level-set curves.
example :
    (∃ φ : ℝ → ℝ × ℝ, φ 0 = 0 ∧ HasDerivAt φ (0, 1) 0 ∧
      ∀ᶠ t in 𝓝 0, (φ t).1 = 0) ∧
    ∃ γ : ℝ → ℝ × ℝ, γ 0 = 0 ∧ HasDerivAt γ (0, 1) 0 ∧ ∀ t, (γ t).1 = 0 := by
  let fst : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  have hsurj : Function.Surjective fst := by
    intro y
    exact ⟨(y, 0), rfl⟩
  constructor
  · simpa [fst] using HasStrictFDerivAt.exists_levelSet_curve
      (f := (Prod.fst : ℝ × ℝ → ℝ)) (f' := fst) (x := (0 : ℝ × ℝ))
      (v := (0, 1)) hasStrictFDerivAt_fst hsurj (by simp [fst])
  · apply levelSet_curve_of_tangent_vel
        (f := (Prod.fst : ℝ × ℝ → ℝ)) (c := 0) (x := (0 : ℝ × ℝ))
        (v := (0, 1))
    · simpa [fst] using fst.contDiff
    · rfl
    · rw [fderiv_fst]
      exact hsurj
    · rw [fderiv_fst]
      rfl

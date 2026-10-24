/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/ODE/Duhamel.lean -/


import sympy.atlas.Analysis.ODE.Duhamel

open MathlibExt.Analysis.ODE.DuhamelWanted

-- Zero operator and unit forcing give the identity solution.
example : ∃ x : ℝ → ℝ, x = id ∧ ∀ t, HasDerivAt x 1 t := by
  let A : ℝ →L[ℝ] ℝ := 0
  obtain ⟨x, _, hx, hdx, _⟩ :=
    duhamel_variation_of_constants A (fun _ => 1) 0 0 continuous_const
  refine ⟨x, ?_, ?_⟩
  · funext t
    simpa [A] using hx t
  · intro t
    simpa [A] using hdx t

-- The uniqueness clause identifies every solution with the explicit solution.
example (y : ℝ → ℝ) (hy₀ : y 0 = 0) (hy : ∀ t, HasDerivAt y 1 t) : y = id := by
  let A : ℝ →L[ℝ] ℝ := 0
  obtain ⟨x, _, hx, _, h_unique⟩ :=
    duhamel_variation_of_constants A (fun _ => 1) 0 0 continuous_const
  calc
    y = x := h_unique y hy₀ (by
      intro t
      simpa [A] using hy t)
    _ = id := by
      funext t
      simpa [A] using hx t

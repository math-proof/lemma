/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/InnerProductSpace/BoundedSelfAdjointSpectral.lean -/


import sympy.atlas.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral


namespace MathlibExtTest.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral

open MeasureTheory MathlibExt.Analysis.InnerProductSpace.BoundedSelfAdjointSpectralWanted

noncomputable section

-- The scalar spectral measure of the identity has total mass equal to the squared norm.
example (v : EuclideanSpace ℂ (Fin 2)) :
    ∃ μ : Measure (spectrum ℂ (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ]
        EuclideanSpace ℂ (Fin 2))),
      IsFiniteMeasure μ ∧ μ.Regular ∧ μ.real Set.univ = ‖v‖ ^ 2 := by
  let T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) := 1
  have hT : IsSelfAdjoint T := IsSelfAdjoint.one _
  obtain ⟨μ, hμfin, hμreg, hμ⟩ := hT.exists_spectralMeasure T v
  refine ⟨μ, hμfin, hμreg, ?_⟩
  let f : C(spectrum ℂ T, ℝ) := ⟨fun _ => 1, continuous_const⟩
  let q : C(spectrum ℂ T, ℂ) := ⟨fun _ => 1, continuous_const⟩
  have h := hμ f
  change (∫ _ : spectrum ℂ T, (1 : ℝ) ∂μ) =
    Complex.re (inner ℂ ((cfcHom hT.isStarNormal) q v) v) at h
  have hq : q = 1 := by
    ext z
    simp [q]
  rw [integral_const, smul_eq_mul, mul_one, hq, map_one, one_apply_eq_self] at h
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact h

-- The multiplication model of the identity on `ℂ²` necessarily uses a nonzero measure.
example :
    ∃ (X : Type) (_ : MeasurableSpace X) (μ : Measure X), μ ≠ 0 := by
  let E := EuclideanSpace ℂ (Fin 2)
  let T : E →L[ℂ] E := 1
  have hT : IsSelfAdjoint T := IsSelfAdjoint.one _
  obtain ⟨X, mX, μ, _φ, _hφ, U, _hU⟩ :=
    boundedSelfAdjoint_spectral_multiplication T hT
  refine ⟨X, mX, μ, ?_⟩
  intro hμ
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hUv : U v = U 0 := by
    apply Lp.ext
    have hae : ae μ = ⊥ := by
      rw [hμ]
      simp
    change Filter.Eventually (fun a => U v a = U 0 a) (ae μ)
    rw [hae]
    simp
  exact hv (U.injective hUv)

end
end MathlibExtTest.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral

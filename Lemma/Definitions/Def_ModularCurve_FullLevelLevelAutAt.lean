import Lemma.Definitions.Def_ModularCurve_FullLevelJacobian

set_option autoImplicit false

noncomputable section

open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace ModularCurve.FullLevel

def conjElemN (m : ℕ) [NeZero m] (γ : SL(2, ℤ)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / m; (m : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)]
    (by
      have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
      have hdet : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) = 1 := by
        have h := Matrix.SpecialLinearGroup.det_coe γ
        rw [Matrix.det_fin_two] at h
        exact_mod_cast h
      rw [Matrix.det_fin_two_of]
      have : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) / m * ((m : ℝ) * ((γ 1 0 : ℤ) : ℝ)) =
          ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) := by
        field_simp
      rw [this, hdet]
      exact one_ne_zero)

def IsLevelAutAt (L : Type) [Field L] [CharZero L] (n : ℕ) (ζ : L) (m : ℕ) [NeZero m]
    (N₀ : ℕ) (H : Subgroup (ZMod N₀)ˣ) (γ : SL(2, ℤ))
    (K : IntermediateField L (LaurentSeries L)) (τ : ↥K ≃ₐ[L] ↥K) : Prop :=
  ∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH N₀ H : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg : PowerSeries ℤ) (_hf : IsIntegralQExp f pf) (_hg : IsIntegralQExp g pg)
    (_hg0 : intSeriesC ℚ pg ≠ 0)
    (x : ↥K) (_hx : ((x : ↥K) : LaurentSeries L) = coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg))
    (ι : L →+* ℂ), ι ζ = Complex.exp (2 * Real.pi * Complex.I / n) →
      coeffMap ι ((τ x : ↥K) : LaurentSeries L) *
          HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] conjElemN m γ)) =
        HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] conjElemN m γ))

end ModularCurve.FullLevel

end

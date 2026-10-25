import Structure.LanglandsTunnell_CubicInduction_Structure

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm

noncomputable section

namespace LanglandsTunnell.CubicInduction

structure CubicInductionData where

  form : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ

  whittaker : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ

  whittakerLoc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ

  whittakerArch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ

  centralChar : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ

  dualWhittaker : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ

structure IsCubicInductionDataOn (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (S : Set (HeightOneSpectrum (𝓞 ℚ))) (X : CubicInductionData) : Prop where
  automorphic : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
    X.form (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = X.form g
  central : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
    X.form (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (X.centralChar z : ℂ) * X.form g
  centralChar_ideleClass : IsIdeleClassChar (𝓞 ℚ) ℚ X.centralChar
  cuspidalP21 : IsCuspidalAlongP21 pins X.form
  cuspidalP12 : IsCuspidalAlongP12 pins X.form
  whittaker_eq : ∀ g, X.whittaker g = whittaker3 pins ψ X.form g
  whittaker_law : IsGL3PsiWhittakerFn ψ X.whittaker
  expansion : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
    HasSum (fun i : MirabolicIndex ℚ => X.whittaker (mirabolicTranslate i * g)) (X.form g)
  whittakerLoc_law : ∀ v, IsGL3PsiWhittakerFn (psiLoc ψ v) (X.whittakerLoc v)
  factorizable : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))),
    (∀ v, v ∈ S → v ∈ T) →
    (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
    X.whittaker g = X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g) *
      ∏ v ∈ T, X.whittakerLoc v (componentAt3 (𝓞 ℚ) ℚ v g)
  spherical : ∀ v, v ∉ S →
    IsInducedSphericalAt (inducedCoeff K μ) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) (X.whittakerLoc v)
  levelInvariant : ∀ v, v ∉ S → ¬ IsRamifiedIn K v →
    ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v), ∀ g, X.whittakerLoc v (g * k) = X.whittakerLoc v g
  multOne : ∀ v, HasWhittakerMultOne (psiLoc ψ v) (X.whittakerLoc v)
  moderateGrowth : IsModerateGrowth3 ℚ X.form
  kFinite : IsKFinite X.whittakerArch
  iotaMoments : HasIotaMoments X.form
  whittakerHalfPlane : HasWhittakerHalfPlane X.whittaker
  dualWhittaker_eq : ∀ g, X.dualWhittaker g = whittaker3 pins ψ⁻¹ (dualForm X.form) g
  dualWhittaker_law : IsGL3PsiWhittakerFn ψ⁻¹ X.dualWhittaker
  dual_expansion : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
    HasSum (fun i : MirabolicIndex ℚ => X.dualWhittaker (mirabolicTranslate i * g)) (dualForm X.form g)
  dual_iotaMoments : HasIotaMoments (dualForm X.form)
  dual_whittakerHalfPlane : HasWhittakerHalfPlane X.dualWhittaker

end LanglandsTunnell.CubicInduction
end

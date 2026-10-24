import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp

open NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace

namespace LanglandsTunnell.CubicInduction.SlabL2

def IsSpectralTranslation3 (h : AdelicGL 3 (𝓞 ℚ) ℚ) : Prop :=
  h ∈ (archComponent3 (𝓞 ℚ) ℚ).ker ∨
    ((∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p h = 1) ∧
      (archComponent3 (𝓞 ℚ) ℚ h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))ᵀ *
          (archComponent3 (𝓞 ℚ) ℚ h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) = 1)

def IsCuspLift3 (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (op : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))
    (T : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)) : Prop :=
  ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀),
    ∃ hRF : op F ∈ cuspFunctions ω a b Φ₀,
      (T ⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩ : Carrier a b Φ₀) =
        toL2 ω a b Φ₀ ⟨op F, hRF.1⟩

def spectralGenerators3 (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    Set (↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)) :=
  {T | ∃ h : AdelicGL 3 (𝓞 ℚ) ℚ, IsSpectralTranslation3 h ∧ IsCuspLift3 ω a b Φ₀ (translateRight h) T} ∪
    {T | ∃ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ ∧ IsCuspLift3 ω a b Φ₀ (smoothingOperator φ) T}

def spectralOperators3 (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    Set (↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)) :=
  spectralGenerators3 ω a b Φ₀ ∪
    {T | ∃ S ∈ spectralGenerators3 ω a b Φ₀,
      ∀ x y : ↥(cuspidalSubspace ω a b Φ₀), ⟪T x, y⟫_ℂ = ⟪x, S y⟫_ℂ}

end LanglandsTunnell.CubicInduction.SlabL2

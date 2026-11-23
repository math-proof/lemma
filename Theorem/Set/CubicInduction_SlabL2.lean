module

public import Theorem.Matrix.CubicInduction_Carrier
public import Theorem.Measure.TateGlobalZeta
public import Mathlib.MeasureTheory.Function.L2Space

public noncomputable section

set_option autoImplicit false

noncomputable section

open NumberField MeasureTheory Measure
open scoped ENNReal

namespace LanglandsTunnell.CubicInduction.SlabL2

attribute [local instance] NumberField.AdelicHaar.glBorel


public theorem mem_ideleNormDetSlab_iff (a b : ℝ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    g ∈ ideleNormDetSlab a b ↔ NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b :=
  Iff.rfl


public theorem slabMeasure_def (a b : ℝ) :
    slabMeasure a b = (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).restrict (ideleNormDetSlab a b) := rfl


public theorem domainMeasure_def (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    domainMeasure a b Φ₀ = (slabMeasure a b).restrict Φ₀ := rfl


public theorem isSlabDomain_iff (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    IsSlabDomain a b Φ₀ ↔ 0 < a ∧ a < b ∧ IsFundamentalDomain (globalPointsGL 3 (𝓞 ℚ) ℚ).range Φ₀ (slabMeasure a b) :=
  Iff.rfl


public theorem IsSlabDomain.pos {a b : ℝ} {Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (h : IsSlabDomain a b Φ₀) : 0 < a := h.1


public theorem IsSlabDomain.lt {a b : ℝ} {Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (h : IsSlabDomain a b Φ₀) : a < b := h.2.1


public theorem IsSlabDomain.isFundamentalDomain {a b : ℝ} {Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (h : IsSlabDomain a b Φ₀) :
    IsFundamentalDomain (globalPointsGL 3 (𝓞 ℚ) ℚ).range Φ₀ (slabMeasure a b) := h.2.2


public theorem mem_automorphicSubmodule_iff (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    f ∈ automorphicSubmodule ω a b Φ₀ ↔
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g) ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g) ∧
      MemLp f 2 (domainMeasure a b Φ₀) :=
  Iff.rfl


public theorem toL2_apply (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (f : ↥(automorphicSubmodule ω a b Φ₀)) :
    toL2 ω a b Φ₀ f = f.2.2.2.toLp (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := rfl

end LanglandsTunnell.CubicInduction.SlabL2

end

module

public import Def.LanglandsTunnell_CubicInduction_Carrier
public import Theorem.Measure.TateGlobalZeta
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField MeasureTheory Measure
open scoped ENNReal

namespace LanglandsTunnell.CubicInduction.SlabL2

attribute [local instance] NumberField.AdelicHaar.glBorel

def ideleNormDetSlab (a b : ℝ) : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}

def slabMeasure (a b : ℝ) : Measure (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).restrict (ideleNormDetSlab a b)

def domainMeasure (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) : Measure (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  (slabMeasure a b).restrict Φ₀

abbrev Carrier (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) : Type :=
  Lp ℂ 2 (domainMeasure a b Φ₀)

def IsSlabDomain (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) : Prop :=
  0 < a ∧ a < b ∧ IsFundamentalDomain (globalPointsGL 3 (𝓞 ℚ) ℚ).range Φ₀ (slabMeasure a b)

def automorphicSubmodule (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) where
  carrier := {f | (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g) ∧
    (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g) ∧
    MemLp f 2 (domainMeasure a b Φ₀)}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => by simp, MemLp.zero⟩
  add_mem' := fun {f f'} hf hf' =>
    ⟨fun γ g => by rw [Pi.add_apply, Pi.add_apply, hf.1, hf'.1],
      fun z g => by rw [Pi.add_apply, Pi.add_apply, hf.2.1, hf'.2.1, mul_add], hf.2.2.add hf'.2.2⟩
  smul_mem' := fun c {f} hf =>
    ⟨fun γ g => by rw [Pi.smul_apply, Pi.smul_apply, hf.1],
      fun z g => by rw [Pi.smul_apply, Pi.smul_apply, hf.2.1, smul_eq_mul, smul_eq_mul, mul_left_comm],
      hf.2.2.const_smul c⟩

def toL2 (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    ↥(automorphicSubmodule ω a b Φ₀) →ₗ[ℂ] Carrier a b Φ₀ where
  toFun f := f.2.2.2.toLp (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
  map_add' f f' := MemLp.toLp_add f.2.2.2 f'.2.2.2
  map_smul' c f := MemLp.toLp_const_smul c f.2.2.2

end LanglandsTunnell.CubicInduction.SlabL2

end

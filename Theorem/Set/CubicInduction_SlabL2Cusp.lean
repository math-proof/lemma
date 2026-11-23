module

public import Theorem.Set.CubicInduction_SlabL2
public import Theorem.Matrix.CubicInduction_Structure
public import Mathlib.Analysis.Calculus.ContDiff.Defs

public noncomputable section

set_option autoImplicit false

noncomputable section

open NumberField MeasureTheory AutomorphicForm IsDedekindDomain
open scoped ENNReal

namespace LanglandsTunnell.CubicInduction.SlabL2

attribute [local instance] NumberField.AdelicHaar.glBorel


public theorem mem_cuspFunctions_iff (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    F ∈ cuspFunctions ω a b Φ₀ ↔ F ∈ automorphicSubmodule ω a b Φ₀ ∧ Continuous F ∧
      IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) F ∧
      IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) F :=
  Iff.rfl


public theorem automorphicSubmodule_of_mem_cuspFunctions (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀) :
    F ∈ automorphicSubmodule ω a b Φ₀ :=
  hF.1


public theorem mem_cuspMembers_iff (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (f : ↥(automorphicSubmodule ω a b Φ₀)) :
    f ∈ cuspMembers ω a b Φ₀ ↔ (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈ cuspFunctions ω a b Φ₀ :=
  Iff.rfl


public theorem cuspidalSubspace_def (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    cuspidalSubspace ω a b Φ₀ =
      (Submodule.span ℂ (toL2 ω a b Φ₀ '' cuspMembers ω a b Φ₀)).topologicalClosure := rfl


public theorem isClosed_cuspidalSubspace (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    IsClosed (cuspidalSubspace ω a b Φ₀ : Set (Carrier a b Φ₀)) :=
  Submodule.isClosed_topologicalClosure _


public theorem toL2_mem_cuspidalSubspace (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    {f : ↥(automorphicSubmodule ω a b Φ₀)} (hf : f ∈ cuspMembers ω a b Φ₀) :
    toL2 ω a b Φ₀ f ∈ cuspidalSubspace ω a b Φ₀ :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, hf, rfl⟩)


public theorem toL2_mem_cuspidalSubspace_of_mem_cuspFunctions (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀) :
    toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ cuspidalSubspace ω a b Φ₀ :=
  toL2_mem_cuspidalSubspace ω a b Φ₀ (f := ⟨F, hF.1⟩) hF


public theorem translateRight_apply (h : AdelicGL 3 (𝓞 ℚ) ℚ) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    translateRight h f x = f (x * h) := rfl


public theorem translateRight_one (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : translateRight 1 f = f := by
  funext x; simp [translateRight]


public theorem translateRight_mul (h h' : AdelicGL 3 (𝓞 ℚ) ℚ) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    translateRight (h * h') f = translateRight h (translateRight h' f) := by
  funext x; simp [translateRight, mul_assoc]


public theorem smoothingOperator_apply (φ f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    smoothingOperator φ f x = ∫ g, φ g * f (x * g) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := rfl

end LanglandsTunnell.CubicInduction.SlabL2

end

import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2
import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option autoImplicit false

noncomputable section

open NumberField MeasureTheory AutomorphicForm IsDedekindDomain
open scoped ENNReal

namespace LanglandsTunnell.CubicInduction.SlabL2

attribute [local instance] NumberField.AdelicHaar.glBorel

def cuspFunctions (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :=
  {F | F ∈ automorphicSubmodule ω a b Φ₀ ∧ Continuous F ∧
    IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) F ∧
    IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) F}

theorem mem_cuspFunctions_iff (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    F ∈ cuspFunctions ω a b Φ₀ ↔ F ∈ automorphicSubmodule ω a b Φ₀ ∧ Continuous F ∧
      IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) F ∧
      IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) F :=
  Iff.rfl

theorem automorphicSubmodule_of_mem_cuspFunctions (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀) :
    F ∈ automorphicSubmodule ω a b Φ₀ :=
  hF.1

def cuspMembers (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    Set ↥(automorphicSubmodule ω a b Φ₀) :=
  {f | (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈ cuspFunctions ω a b Φ₀}

theorem mem_cuspMembers_iff (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (f : ↥(automorphicSubmodule ω a b Φ₀)) :
    f ∈ cuspMembers ω a b Φ₀ ↔ (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈ cuspFunctions ω a b Φ₀ :=
  Iff.rfl

def cuspidalSubspace (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    Submodule ℂ (Carrier a b Φ₀) :=
  (Submodule.span ℂ (toL2 ω a b Φ₀ '' cuspMembers ω a b Φ₀)).topologicalClosure

theorem cuspidalSubspace_def (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    cuspidalSubspace ω a b Φ₀ =
      (Submodule.span ℂ (toL2 ω a b Φ₀ '' cuspMembers ω a b Φ₀)).topologicalClosure := rfl

theorem isClosed_cuspidalSubspace (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    IsClosed (cuspidalSubspace ω a b Φ₀ : Set (Carrier a b Φ₀)) :=
  Submodule.isClosed_topologicalClosure _

theorem toL2_mem_cuspidalSubspace (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    {f : ↥(automorphicSubmodule ω a b Φ₀)} (hf : f ∈ cuspMembers ω a b Φ₀) :
    toL2 ω a b Φ₀ f ∈ cuspidalSubspace ω a b Φ₀ :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, hf, rfl⟩)

theorem toL2_mem_cuspidalSubspace_of_mem_cuspFunctions (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀) :
    toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ cuspidalSubspace ω a b Φ₀ :=
  toL2_mem_cuspidalSubspace ω a b Φ₀ (f := ⟨F, hF.1⟩) hF

def realCoordinate : InfiniteAdeleRing ℚ →+* ℝ :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).toRingHom.comp
    (Pi.evalRingHom (fun v : InfinitePlace ℚ => v.Completion) Rat.infinitePlace)

def archEntries (g : AdelicGL 3 (𝓞 ℚ) ℚ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => realCoordinate ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).1

def IsSmoothArchFactor (α : (Fin 3 → Fin 3 → ℝ) → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) α ∧ HasCompactSupport α ∧ tsupport α ⊆ {m | (Matrix.of m).det ≠ 0}

def IsSmoothingKernel (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  ∃ (α : (Fin 3 → Fin 3 → ℝ) → ℂ) (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))),
    IsSmoothArchFactor α ∧
    (∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
      IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ)))) ∧
    (∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
    ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      φ g = α (archEntries g) *
        Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) g

def translateRight (h : AdelicGL 3 (𝓞 ℚ) ℚ) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
  fun x => f (x * h)

theorem translateRight_apply (h : AdelicGL 3 (𝓞 ℚ) ℚ) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    translateRight h f x = f (x * h) := rfl

theorem translateRight_one (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : translateRight 1 f = f := by
  funext x; simp [translateRight]

theorem translateRight_mul (h h' : AdelicGL 3 (𝓞 ℚ) ℚ) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    translateRight (h * h') f = translateRight h (translateRight h' f) := by
  funext x; simp [translateRight, mul_assoc]

def smoothingOperator (φ f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
  fun x => ∫ g, φ g * f (x * g) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)

theorem smoothingOperator_apply (φ f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    smoothingOperator φ f x = ∫ g, φ g * f (x * g) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := rfl

end LanglandsTunnell.CubicInduction.SlabL2

end

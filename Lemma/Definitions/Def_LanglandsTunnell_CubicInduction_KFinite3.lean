import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_EnvelopingAction3

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction

namespace LanglandsTunnell.CubicInduction.WhittakerBlock

def IsOrthFinite (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
  (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
    (fun g => f (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))

def orthSpan (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :=
  Submodule.span ℂ {φ | ∃ k : AdelicGL 3 (𝓞 ℚ) ℚ,
    (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) ∧ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      φ = fun g => f (g * k)}

open scoped LanglandsTunnell.CubicInduction.WhittakerBlock in

def gKSpan (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Submodule envelopingAlgebra3 smoothFunctions3 :=
  Submodule.span envelopingAlgebra3 {φ : smoothFunctions3 | (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈ orthSpan f}

end LanglandsTunnell.CubicInduction.WhittakerBlock

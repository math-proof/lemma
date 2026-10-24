import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField

namespace LanglandsTunnell.CubicInduction

def IsLocalWhittakerDatum (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (W : LocalGL3 v → ℂ) : Prop :=
  IsGL3PsiWhittakerFn ψv W ∧ W 1 = 1 ∧
    HasWhittakerMultOne ψv W ∧
    (∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F) ∧
    (∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g) ∧
    ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))

end LanglandsTunnell.CubicInduction

end

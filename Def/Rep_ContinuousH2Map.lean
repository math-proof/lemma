module

public import Mathlib
public import Def.Submodule_ContinuousH2

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace groupCohomology

variable {k : Type u} [CommRing k] {G H : Type u} [Group G] [Group H]
variable {rH : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
  {rG : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
  (f : G →* H) (hf : ∀ g, rH (f g) = rG g)

section precomp

include hf

end precomp

variable {A : Rep k H} {B : Rep k G} (φ : A →ₗ[k] B) (hφ : ∀ (g : G) (a : A), φ (A.ρ (f g) a) = B.ρ g (φ a))

def cochainsPullPush₁ : (H → A) →ₗ[k] (G → B) where
  toFun x := φ ∘ x ∘ f
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

def cochainsPullPush₂ : (H × H → A) →ₗ[k] (G × G → B) where
  toFun x := φ ∘ x ∘ Prod.map f f
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

def levelCocycles₂Map : ↥(levelCocycles₂ rH A) →ₗ[k] ↥(levelCocycles₂ rG B) :=
  (cochainsPullPush₂ f φ).restrict fun _ hx => cochainsPullPush₂_mem_levelCocycles₂ f hf φ hφ hx

def continuousH2Map : continuousH2 rH A →ₗ[k] continuousH2 rG B :=
  Submodule.mapQ _ _ (levelCocycles₂Map f hf φ hφ) fun _ hx =>
    cochainsPullPush₂_mem_levelCoboundaries₂ f hf φ hφ hx

end groupCohomology

end

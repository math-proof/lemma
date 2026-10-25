import Mathlib
import Lemma.GroupCohomology.ContinuousH2

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

lemma IsLevelConstant₁.precomp {X : Type*} {x : H → X} (hx : IsLevelConstant₁ rH x) :
    IsLevelConstant₁ rG (x ∘ f) := by
  obtain ⟨F, hF, h⟩ := hx
  refine ⟨F, hF, fun g s hs => ?_⟩
  simp only [Function.comp_apply, map_mul]
  exact h (f g) (f s) (by rwa [hf])

lemma IsLevelConstant₂.precomp {X : Type*} {x : H × H → X} (hx : IsLevelConstant₂ rH x) :
    IsLevelConstant₂ rG (x ∘ Prod.map f f) := by
  obtain ⟨F, hF, h⟩ := hx
  refine ⟨F, hF, fun g g' s s' hs hs' => ?_⟩
  simp only [Function.comp_apply, Prod.map_apply, map_mul]
  exact h (f g) (f g') (f s) (f s') (by rwa [hf]) (by rwa [hf])

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

@[simp] lemma cochainsPullPush₁_apply (x : H → A) (g : G) : cochainsPullPush₁ f φ x g = φ (x (f g)) := rfl

@[simp] lemma cochainsPullPush₂_apply (x : H × H → A) (g : G × G) :
    cochainsPullPush₂ f φ x g = φ (x (f g.1, f g.2)) := rfl

include hφ in
lemma cochainsPullPush₂_d₁₂ (x : H → A) :
    cochainsPullPush₂ f φ ((d₁₂ A).hom x) = (d₁₂ B).hom (cochainsPullPush₁ f φ x) := by
  ext ⟨g, g'⟩
  simp [d₁₂_hom_apply, map_add, map_sub, hφ, map_mul]

include hφ in
lemma cochainsPullPush₂_mem_cocycles₂ {x : H × H → A} (hx : x ∈ cocycles₂ A) :
    cochainsPullPush₂ f φ x ∈ cocycles₂ B := by
  rw [mem_cocycles₂_iff] at hx ⊢
  intro g h j
  simp only [cochainsPullPush₂_apply, map_mul, ← map_add, hx, ← hφ]

include hf in
lemma cochainsPullPush₁_mem_levelCochains₁ {x : H → A} (hx : x ∈ levelCochains₁ rH A) :
    cochainsPullPush₁ f φ x ∈ levelCochains₁ rG B :=
  ((IsLevelConstant₁.precomp f hf hx).comp φ :)

include hf in
lemma cochainsPullPush₂_mem_levelCochains₂ {x : H × H → A} (hx : x ∈ levelCochains₂ rH A) :
    cochainsPullPush₂ f φ x ∈ levelCochains₂ rG B :=
  ((IsLevelConstant₂.precomp f hf hx).comp φ :)

include hf hφ in
lemma cochainsPullPush₂_mem_levelCocycles₂ {x : H × H → A} (hx : x ∈ levelCocycles₂ rH A) :
    cochainsPullPush₂ f φ x ∈ levelCocycles₂ rG B :=
  ⟨cochainsPullPush₂_mem_cocycles₂ f φ hφ hx.1, cochainsPullPush₂_mem_levelCochains₂ f hf φ hx.2⟩

include hf hφ in
lemma cochainsPullPush₂_mem_levelCoboundaries₂ {x : H × H → A} (hx : x ∈ levelCoboundaries₂ rH A) :
    cochainsPullPush₂ f φ x ∈ levelCoboundaries₂ rG B := by
  obtain ⟨y, hy, rfl⟩ := (mem_levelCoboundaries₂_iff rH A x).1 hx
  exact (mem_levelCoboundaries₂_iff rG B _).2
    ⟨cochainsPullPush₁ f φ y, IsLevelConstant₁.precomp f hf hy |>.comp φ, (cochainsPullPush₂_d₁₂ f φ hφ y).symm⟩

def levelCocycles₂Map : ↥(levelCocycles₂ rH A) →ₗ[k] ↥(levelCocycles₂ rG B) :=
  (cochainsPullPush₂ f φ).restrict fun _ hx => cochainsPullPush₂_mem_levelCocycles₂ f hf φ hφ hx

@[simp] lemma coe_levelCocycles₂Map (x : ↥(levelCocycles₂ rH A)) :
    (levelCocycles₂Map f hf φ hφ x : G × G → B) = cochainsPullPush₂ f φ x := rfl

def continuousH2Map : continuousH2 rH A →ₗ[k] continuousH2 rG B :=
  Submodule.mapQ _ _ (levelCocycles₂Map f hf φ hφ) fun _ hx =>
    cochainsPullPush₂_mem_levelCoboundaries₂ f hf φ hφ hx

@[simp] lemma continuousH2Map_continuousH2π (x : ↥(levelCocycles₂ rH A)) :
    continuousH2Map f hf φ hφ (continuousH2π rH A x) = continuousH2π rG B (levelCocycles₂Map f hf φ hφ x) :=
  rfl

end groupCohomology

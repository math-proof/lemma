import Mathlib
import Lemma.Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace groupCohomology

universe u

variable {k : Type u} [CommRing k] {G H I : Type u} [Group G] [Group H] [Group I]
variable {rI : I →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} {rH : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
  {rG : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
  (f : G →* H) (hf : ∀ g, rH (f g) = rG g) (S : Finset Nat.Primes)

section precomp

include hf

lemma IsLevelConstantSr₁.precomp {X : Type*} {x : H → X} (hx : IsLevelConstantSr₁ rH S x) : IsLevelConstantSr₁ rG S (x ∘ f) := by
  obtain ⟨F, hF, h⟩ := hx
  refine ⟨F, hF, fun g s hs => ?_⟩
  simp only [Function.comp_apply, map_mul]
  exact h (f g) (f s) (by rwa [hf])

lemma IsLevelConstantSr₂.precomp {X : Type*} {x : H × H → X} (hx : IsLevelConstantSr₂ rH S x) :
    IsLevelConstantSr₂ rG S (x ∘ Prod.map f f) := by
  obtain ⟨F, hF, h⟩ := hx
  refine ⟨F, hF, fun g g' s s' hs hs' => ?_⟩
  simp only [Function.comp_apply, Prod.map_apply, map_mul]
  exact h (f g) (f g') (f s) (f s') (by rwa [hf]) (by rwa [hf])

end precomp

section degreeTwo

variable {A : Rep k H} {B : Rep k G} (φ : A →ₗ[k] B) (hφ : ∀ (g : G) (a : A), φ (A.ρ (f g) a) = B.ρ g (φ a))

include hf in
lemma cochainsPullPush₁_mem_levelCochainsSr₁ {x : H → A} (hx : x ∈ levelCochainsSr₁ rH S A) :
    cochainsPullPush₁ f φ x ∈ levelCochainsSr₁ rG S B :=
  ((IsLevelConstantSr₁.precomp f hf S hx).comp φ :)

include hf in
lemma cochainsPullPush₂_mem_levelCochainsSr₂ {x : H × H → A} (hx : x ∈ levelCochainsSr₂ rH S A) :
    cochainsPullPush₂ f φ x ∈ levelCochainsSr₂ rG S B :=
  ((IsLevelConstantSr₂.precomp f hf S hx).comp φ :)

include hf hφ in
lemma cochainsPullPush₂_mem_levelCocyclesSr₂ {x : H × H → A} (hx : x ∈ levelCocyclesSr₂ rH S A) :
    cochainsPullPush₂ f φ x ∈ levelCocyclesSr₂ rG S B :=
  ⟨cochainsPullPush₂_mem_cocycles₂ f φ hφ hx.1, cochainsPullPush₂_mem_levelCochainsSr₂ f hf S φ hx.2⟩

include hf hφ in
lemma cochainsPullPush₂_mem_levelCoboundariesSr₂ {x : H × H → A} (hx : x ∈ levelCoboundariesSr₂ rH S A) :
    cochainsPullPush₂ f φ x ∈ levelCoboundariesSr₂ rG S B := by
  obtain ⟨y, hy, rfl⟩ := (mem_levelCoboundariesSr₂_iff rH S A x).1 hx
  exact (mem_levelCoboundariesSr₂_iff rG S B _).2
    ⟨cochainsPullPush₁ f φ y, (IsLevelConstantSr₁.precomp f hf S hy).comp φ, (cochainsPullPush₂_d₁₂ f φ hφ y).symm⟩

def levelCocyclesSr₂Map : ↥(levelCocyclesSr₂ rH S A) →ₗ[k] ↥(levelCocyclesSr₂ rG S B) :=
  (cochainsPullPush₂ f φ).restrict fun _ hx => cochainsPullPush₂_mem_levelCocyclesSr₂ f hf S φ hφ hx

@[simp] lemma coe_levelCocyclesSr₂Map (x : ↥(levelCocyclesSr₂ rH S A)) :
    (levelCocyclesSr₂Map f hf S φ hφ x : G × G → B) = cochainsPullPush₂ f φ x := rfl

def continuousH2SrMap : continuousH2Sr rH S A →ₗ[k] continuousH2Sr rG S B :=
  Submodule.mapQ _ _ (levelCocyclesSr₂Map f hf S φ hφ) fun _ hx => cochainsPullPush₂_mem_levelCoboundariesSr₂ f hf S φ hφ hx

@[simp] lemma continuousH2SrMap_continuousH2Srπ (x : ↥(levelCocyclesSr₂ rH S A)) :
    continuousH2SrMap f hf S φ hφ (continuousH2Srπ rH S A x) = continuousH2Srπ rG S B (levelCocyclesSr₂Map f hf S φ hφ x) := rfl

lemma continuousH2SrToContinuousH2_comp_continuousH2SrMap :
    continuousH2SrToContinuousH2 rG S B ∘ₗ continuousH2SrMap f hf S φ hφ =
      continuousH2Map f hf φ hφ ∘ₗ continuousH2SrToContinuousH2 rH S A :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

variable {S} in

lemma continuousH2SrOfLE_comp_continuousH2SrMap {S' : Finset Nat.Primes} (h : S ⊆ S') :
    continuousH2SrOfLE rG B h ∘ₗ continuousH2SrMap f hf S φ hφ = continuousH2SrMap f hf S' φ hφ ∘ₗ continuousH2SrOfLE rH A h :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

end degreeTwo

section laws

variable {A : Rep k G}

lemma continuousH2SrMap_id :
    continuousH2SrMap (rH := rG) (MonoidHom.id G) (fun _ => rfl) S (LinearMap.id : A →ₗ[k] A) (fun _ _ => rfl) = LinearMap.id :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

variable {B : Rep k H} {C : Rep k I} (f' : H →* I) (hf' : ∀ h, rI (f' h) = rH h)
  (ψ : C →ₗ[k] B) (hψ : ∀ (h : H) (c : C), ψ (C.ρ (f' h) c) = B.ρ h (ψ c))
  (φ : B →ₗ[k] A) (hφ : ∀ (g : G) (b : B), φ (B.ρ (f g) b) = A.ρ g (φ b))

lemma continuousH2SrMap_comp :
    continuousH2SrMap (f'.comp f) (fun g => by rw [MonoidHom.comp_apply, hf', hf]) S (φ ∘ₗ ψ)
        (fun g c => by rw [LinearMap.comp_apply, LinearMap.comp_apply, MonoidHom.comp_apply, hψ, hφ]) =
      continuousH2SrMap f hf S φ hφ ∘ₗ continuousH2SrMap f' hf' S ψ hψ :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

end laws

section sameGroup

variable (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) {A B C : Rep k G}

abbrev continuousH2SrMapHom (φ : A ⟶ B) : continuousH2Sr r S A →ₗ[k] continuousH2Sr r S B :=
  continuousH2SrMap (MonoidHom.id G) (fun _ => rfl) S φ.hom.toLinearMap (fun g a => Rep.hom_comm_apply φ g a)

lemma continuousH2SrMapHom_continuousH2Srπ (φ : A ⟶ B) (x : ↥(levelCocyclesSr₂ r S A)) :
    continuousH2SrMapHom S r φ (continuousH2Srπ r S A x) =
      continuousH2Srπ r S B (levelCocyclesSr₂Map (MonoidHom.id G) (fun _ => rfl) S φ.hom.toLinearMap
        (fun g a => Rep.hom_comm_apply φ g a) x) := rfl

lemma continuousH2SrMapHom_id : continuousH2SrMapHom S r (𝟙 A) = LinearMap.id :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

lemma continuousH2SrMapHom_comp (φ : A ⟶ B) (ψ : B ⟶ C) :
    continuousH2SrMapHom S r (φ ≫ ψ) = continuousH2SrMapHom S r ψ ∘ₗ continuousH2SrMapHom S r φ :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

end sameGroup

section degreeOne

variable {A : Rep k H} {B : Rep k G} (φ : Rep.res f A ⟶ B)

lemma coe_mapCocycles₁_apply (c : cocycles₁ A) (g : G) : (mapCocycles₁ f φ c : G → B) g = φ.hom (c (f g)) := rfl

lemma map_hom_H1π (c : cocycles₁ A) :
    (groupCohomology.map f φ 1).hom ((H1π A).hom c) = (H1π B).hom (mapCocycles₁ f φ c) := by
  change (H1π A ≫ groupCohomology.map f φ 1).hom c = (mapCocycles₁ f φ ≫ H1π B).hom c
  rw [H1π_comp_map]

include hf in

lemma map_continuousH1Sr_le :
    (continuousH1Sr rH S A).map (groupCohomology.map f φ 1).hom ≤ continuousH1Sr rG S B := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨c, hc, rfl⟩ := (mem_continuousH1Sr_iff rH S A x).1 hx
  rw [map_hom_H1π]
  refine H1π_mem_continuousH1Sr rG S B ?_
  have hfun : ((mapCocycles₁ f φ c : cocycles₁ B) : G → B) = φ.hom ∘ (c : H → A) ∘ f :=
    funext fun g => coe_mapCocycles₁_apply f φ c g
  rw [hfun]
  exact (IsLevelConstantSr₁.precomp f hf S hc).comp φ.hom

def continuousH1SrMap : ↥(continuousH1Sr rH S A) →ₗ[k] ↥(continuousH1Sr rG S B) :=
  (groupCohomology.map f φ 1).hom.restrict fun x hx => map_continuousH1Sr_le f hf S φ ⟨x, hx, rfl⟩

@[simp] lemma coe_continuousH1SrMap_apply (x : ↥(continuousH1Sr rH S A)) :
    (continuousH1SrMap f hf S φ x : H1 B) = (groupCohomology.map f φ 1).hom x := rfl

end degreeOne

end groupCohomology

end

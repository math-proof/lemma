import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.HCBimoduleProjectives


/--
[tensor_hom_bimodule_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HCBimoduleProjectives.lean)
-/
@[path]
private lemma main
  {R : Type u_R}
  [CommRing R]
  {𝔤 : Type u_𝔤}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {R : Type u_R}
  [CommRing R]
  {𝔤 : Type u_𝔤}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsSemisimple R 𝔤]
  [Module.Finite R 𝔤]
  {θ : CenterCharacter R 𝔤}
  {T : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤}
  {V : Type*}
  [AddCommGroup V]
  [Module R V]
  {ι : V →ₗ[R] T.carrier}
  {Y : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤}
  {f₁ f₂ : T.carrier →ₗ[R] Y.carrier}
-- given
  (h_gen : ∀ t : T.carrier, ∃ (n : ℕ) (vs : Fin n → V) (us : Fin n → (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ), t = ∑ i, T.rightAction (us i) (ι (vs i)))
  (h_f₁_right : ∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (t : T.carrier), f₁ (T.rightAction u t) = Y.rightAction u (f₁ t))
  (h_f₂_right : ∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (t : T.carrier), f₂ (T.rightAction u t) = Y.rightAction u (f₂ t))
  (h_agree_on_V : ∀ v : V, f₁ (ι v) = f₂ (ι v)) :
-- imply
  ∀ t : T.carrier, f₁ t = f₂ t := by
-- proof
  intro t
  obtain ⟨n, vs, us, ht⟩ := h_gen t
  rw [ht]
  simp only [map_sum]
  congr 1
  ext i
  rw [h_f₁_right, h_f₂_right, h_agree_on_V]

/--
[tensor_product_bimodule_surjects_from_generators](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HCBimoduleProjectives.lean)
-/
private lemma tensor_product_bimodule_surjects_from_generators
  {R : Type u_R}
  [CommRing R]
  {𝔤 : Type u_𝔤}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {R : Type u_R}
  [CommRing R]
  {𝔤 : Type u_𝔤}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsSemisimple R 𝔤]
  [Module.Finite R 𝔤]
  {θ : CenterCharacter R 𝔤}
  {Y : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤}
  {V : Type u_mod}
  [AddCommGroup V]
  [Module R V]
  {ι : V →ₗ[R] Y.carrier}
-- given
  (hY : IsInHCThetaOne Y θ)
  (h_gen : ∀ y : Y.carrier, ∃ (n : ℕ) (vs : Fin n → V) (us : Fin n → (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ), y = ∑ i, Y.rightAction (us i) (ι (vs i))) :
-- imply
  ∃ (P : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤) (hP : IsInHCThetaOne P θ), IsTensorProductBimoduleWithUTheta P θ V ∧ ∃ (π : HCThetaOneHom P Y θ hP hY), Function.Surjective π.toLinearMap := by
-- proof
  refine ⟨Y, hY, ?_, ?_⟩
  ·
    refine ⟨Y, ?_, ?_, ?_⟩
    ·
      exact ⟨LinearMap.id, Function.bijective_id, fun _ _ => rfl, fun _ _ => rfl⟩
    ·
      exact ⟨ι, h_gen⟩
    ·
      exact hY.right_annihilated
  ·
    refine ⟨⟨LinearMap.id, fun _ _ => rfl, fun _ _ => rfl⟩, Function.surjective_id⟩


-- created on 2026-10-23
-- updated on 2026-10-24

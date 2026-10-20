import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_exists_spec_map_comp_eq_of_forall_spec_map_comp_eq_of_forall_mem_iff](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_spec_map_comp_eq_of_forall_spec_map_comp_eq_of_forall_mem_iff.lean)
-/
@[path]
private lemma main
    (Ω : Type) [Field Ω] (X : Scheme.{0}) (x : Spec (CommRingCat.of Ω) ⟶ X)
    (S : Set (Ω ≃+* Ω)) (hx : ∀ σ ∈ S, Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x = x)
    (F : Subfield Ω) (hF : ∀ a : Ω, a ∈ F ↔ ∀ σ ∈ S, σ a = a) :
    ∃ y : Spec (CommRingCat.of ↥F) ⟶ X, Spec.map (CommRingCat.ofHom F.subtype) ≫ y = x := by
  classical
  let ξ : X := x.base (IsLocalRing.closedPoint Ω)
  let 𝒰 := X.affineCover
  let j := 𝒰.idx ξ
  have hrange : Set.range x.base ⊆ Set.range (𝒰.f j).base := by
    rintro _ ⟨q, rfl⟩
    have hq : q = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    rw [hq]
    exact 𝒰.covers ξ
  let x' : Spec (CommRingCat.of Ω) ⟶ 𝒰.X j := IsOpenImmersion.lift (𝒰.f j) x hrange
  have hx' : x' ≫ 𝒰.f j = x := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨ψ, hψ⟩ : ∃ ψ : _ ⟶ CommRingCat.of Ω, Spec.map ψ = x' := ⟨Spec.preimage x', Spec.map_preimage x'⟩
  have hinv : ∀ σ ∈ S, ψ ≫ CommRingCat.ofHom (σ : Ω →+* Ω) = ψ := by
    intro σ hσ
    have h1 : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x' = x' := by
      rw [← cancel_mono (𝒰.f j), Category.assoc, hx']
      exact hx σ hσ
    apply Spec.map_injective
    rw [Spec.map_comp, hψ]
    exact h1
  have hmem : ∀ r, ψ.hom r ∈ F := fun r => by
    rw [hF]
    intro σ hσ
    have := congrArg (fun f : _ ⟶ CommRingCat.of Ω => f.hom r) (hinv σ hσ)
    simpa using this
  let ψ' : _ ⟶ CommRingCat.of ↥F := CommRingCat.ofHom (ψ.hom.codRestrict F hmem)
  have hψ' : ψ' ≫ CommRingCat.ofHom F.subtype = ψ := by
    ext r; rfl
  refine ⟨Spec.map ψ' ≫ 𝒰.f j, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp, hψ', hψ]
  exact hx'

-- created on 2026-10-20

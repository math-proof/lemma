import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma exists_retraction {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (s : X.X₃ →ₗ[k] X.X₂) (hs : ∀ x : X.X₃, X.g.hom (s x) = x) : ∃ r : X.X₂ →ₗ[k] X.X₁, LinearMap.comp r X.f.hom.toLinearMap = LinearMap.id := by
  have hinj : Function.Injective X.f.hom.toLinearMap := (Rep.mono_iff_injective X.f).1 hX.mono_f
  have hker : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
    (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
  let φ : X.X₂ →ₗ[k] X.X₂ := LinearMap.id - LinearMap.comp s X.g.hom.toLinearMap
  have hmem : ∀ y, φ y ∈ LinearMap.range X.f.hom.toLinearMap := fun y => by
    rw [hker, LinearMap.mem_ker]
    show X.g.hom (y - s (X.g.hom y)) = 0
    rw [map_sub, hs, sub_self]
  refine ⟨LinearMap.comp ((LinearEquiv.ofInjective _ hinj).symm.toLinearMap) (LinearMap.codRestrict (LinearMap.range X.f.hom.toLinearMap) φ hmem), ?_⟩
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply]
  apply (LinearEquiv.ofInjective _ hinj).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [LinearEquiv.ofInjective_apply, LinearMap.codRestrict_apply]
  show X.f.hom x - s (X.g.hom (X.f.hom x)) = X.f.hom x
  have h0 : X.g.hom (X.f.hom x) = 0 := by
    show X.f.hom.toLinearMap x ∈ LinearMap.ker X.g.hom.toLinearMap
    rw [← hker]
    exact ⟨x, rfl⟩
  rw [h0, map_zero, sub_zero]
/--
[Rep_shortExact_map_tensorRight_of_splitting](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_shortExact_map_tensorRight_of_splitting.lean)
-/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G]
  {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
  (s : X.X₃ →ₗ[k] X.X₂) (hs : ∀ x : X.X₃, X.g.hom (s x) = x) (B : Rep k G) :
  -- imply
  (X.map (MonoidalCategory.tensorRight B)).ShortExact := by
  -- proof
  have hsurj : Function.Surjective X.g.hom.toLinearMap := (Rep.epi_iff_surjective X.g).1 hX.epi_g
  have hker : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
    (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
  have hexact : Function.Exact X.f.hom.toLinearMap X.g.hom.toLinearMap := LinearMap.exact_iff.2 hker.symm
  obtain ⟨r, hr⟩ := exists_retraction hX s hs
  have hT : Function.Exact (X.f.hom.toLinearMap.rTensor B) (X.g.hom.toLinearMap.rTensor B) :=
    rTensor_exact B hexact hsurj
  have hinjA : Function.Injective (X.f.hom.toLinearMap.rTensor B) := by
    refine Function.LeftInverse.injective (g := r.rTensor B) fun t => ?_
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hr, LinearMap.rTensor_id, LinearMap.id_apply]
  have hsurjA : Function.Surjective (X.g.hom.toLinearMap.rTensor B) :=
    LinearMap.rTensor_surjective _ hsurj
  refine
    { exact := (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful _
        ((ShortComplex.moduleCat_exact_iff _).2 fun y hy => by
          obtain ⟨x, hx⟩ := (hT y).1 hy
          exact ⟨x, hx⟩)
      mono_f := (Rep.mono_iff_injective _).2 hinjA
      epi_g := (Rep.epi_iff_surjective _).2 hsurjA }


-- created on 2026-10-20

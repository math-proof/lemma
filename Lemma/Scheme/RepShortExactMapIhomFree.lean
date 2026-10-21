import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma Rep.shortExact_of_hom₄ {k G : Type} [CommRing k] [Group G] {S : ShortComplex (Rep k G)}
    (hf : Function.Injective S.f.hom) (hg : Function.Surjective S.g.hom)
    (hfg : ∀ y : S.X₂, S.g.hom y = 0 ↔ y ∈ Set.range S.f.hom) : S.ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ((Rep.mono_iff_injective _).2 hf) ((Rep.epi_iff_surjective _).2 hg)
  refine Functor.reflects_exact_of_faithful (forget₂ (Rep k G) (ModuleCat k)) _ ?_
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  intro y
  exact hfg y
private lemma Rep.ihom_map_hom_apply_apply {k G : Type} [CommRing k] [Group G] (R : Rep k G) {X Y : Rep k G} (φ : X ⟶ Y)
    (x : (ihom R).obj X) (r : R) :
    (show R →ₗ[k] Y from ((ihom R).map φ).hom x) r = φ.hom ((show R →ₗ[k] X from x) r) := rfl
private lemma Rep.apply_eq_zero_iff_of_shortExact {k G : Type} [CommRing k] [Group G] {X : ShortComplex (Rep k G)}
    (hX : X.ShortExact) (y : X.X₂) : X.g.hom y = 0 ↔ y ∈ Set.range X.f.hom :=
  ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hX.exact.map (forget₂ (Rep k G) (ModuleCat k)))) y
private lemma Rep.ihom_map_hom_injective {k G : Type} [CommRing k] [Group G] (R : Rep k G) {X Y : Rep k G} (φ : X ⟶ Y)
    (hφ : Function.Injective φ.hom) : Function.Injective ((ihom R).map φ).hom := by
  intro x x' h
  have h' : ∀ r : R, (show R →ₗ[k] Y from ((ihom R).map φ).hom x) r = (show R →ₗ[k] Y from ((ihom R).map φ).hom x') r :=
    fun r => by rw [h]
  apply LinearMap.ext
  intro r
  exact hφ (by simpa only [Rep.ihom_map_hom_apply_apply] using h' r)
private lemma Rep.ihom_map_hom_surjective {k G : Type} [CommRing k] [Group G] (V : Type) [AddCommGroup V] [Module k V]
    [Module.Projective k V] (ρ : Representation k G V) {X Y : Rep k G} (φ : X ⟶ Y) (hφ : Function.Surjective φ.hom) :
    Function.Surjective ((ihom (Rep.of ρ)).map φ).hom := by
  intro y
  obtain ⟨h, hh⟩ := Module.projective_lifting_property (φ.hom.toLinearMap) (show V →ₗ[k] Y from y) hφ
  refine ⟨(show (ihom (Rep.of ρ)).obj X from h), ?_⟩
  apply LinearMap.ext
  intro r
  rw [Rep.ihom_map_hom_apply_apply]
  exact LinearMap.congr_fun hh r
private lemma Rep.ihom_map_hom_apply_eq_zero_iff {k G : Type} [CommRing k] [Group G] (R : Rep k G) {X : ShortComplex (Rep k G)}
    (hf : Function.Injective X.f.hom) (hfg : ∀ y : X.X₂, X.g.hom y = 0 ↔ y ∈ Set.range X.f.hom)
    (h : (ihom R).obj X.X₂) : ((ihom R).map X.g).hom h = 0 ↔ h ∈ Set.range ((ihom R).map X.f).hom := by
  constructor
  · intro h0
    have hr : ∀ r : R, (show R →ₗ[k] X.X₂ from h) r ∈ Set.range X.f.hom := fun r => by
      rw [← hfg, ← Rep.ihom_map_hom_apply_apply R X.g h r, h0]
      rfl
    choose s hs using hr
    let h' : R →ₗ[k] X.X₁ :=
      { toFun := s
        map_add' := fun r r' => hf (by rw [map_add, hs, hs, hs, map_add])
        map_smul' := fun c r => hf (by rw [RingHom.id_apply, map_smul, hs, hs, map_smul]) }
    refine ⟨(show (ihom R).obj X.X₁ from h'), ?_⟩
    apply LinearMap.ext
    intro r
    rw [Rep.ihom_map_hom_apply_apply]
    exact hs r
  · rintro ⟨h', rfl⟩
    apply LinearMap.ext
    intro r
    rw [Rep.ihom_map_hom_apply_apply, Rep.ihom_map_hom_apply_apply]
    exact (hfg _).2 ⟨_, rfl⟩
/--
[Rep_shortExact_map_ihom_of_free](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_shortExact_map_ihom_of_free.lean)
-/
@[path]
private lemma main {G : Type} [Group G] (V : Type) [AddCommGroup V] [Module.Free ℤ V]
    (ρ : Representation ℤ G V) {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact) :
    (X.map (ihom (Rep.of ρ))).ShortExact := by
  have hf : Function.Injective X.f.hom := (Rep.mono_iff_injective _).1 hX.mono_f
  have hg : Function.Surjective X.g.hom := (Rep.epi_iff_surjective _).1 hX.epi_g
  have hfg := Rep.apply_eq_zero_iff_of_shortExact hX
  exact Rep.shortExact_of_hom₄ (Rep.ihom_map_hom_injective (Rep.of ρ) X.f hf)
    (Rep.ihom_map_hom_surjective V ρ X.g hg) (Rep.ihom_map_hom_apply_eq_zero_iff (Rep.of ρ) hf hfg)

-- created on 2026-10-20

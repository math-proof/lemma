import Mathlib
import sympy.Basic
open CategoryTheory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma Rep.shortExact_of_hom₄ {k G : Type} [CommRing k] [Group G] {S : ShortComplex (Rep k G)} (hf : Function.Injective S.f.hom) (hg : Function.Surjective S.g.hom) (hfg : ∀ y : S.X₂, S.g.hom y = 0 ↔ y ∈ Set.range S.f.hom) : S.ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ((Rep.mono_iff_injective _).2 hf) ((Rep.epi_iff_surjective _).2 hg)
  refine Functor.reflects_exact_of_faithful (forget₂ (Rep k G) (ModuleCat k)) _ ?_
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  intro y
  apply hfg y

private lemma Rep.ihom_map_hom_apply_apply {k G : Type} [CommRing k] [Group G] (R : Rep k G) {X Y : Rep k G} (φ : X ⟶ Y) (x : (ihom R).obj X) (r : R) : (show R →ₗ[k] Y from ((ihom R).map φ).hom x) r = φ.hom ((show R →ₗ[k] X from x) r) := rfl

private lemma Rep.apply_eq_zero_iff_of_shortExact {k G : Type} [CommRing k] [Group G] {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (y : X.X₂) : X.g.hom y = 0 ↔ y ∈ Set.range X.f.hom := ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hX.exact.map (forget₂ (Rep k G) (ModuleCat k)))) y

private lemma Rep.ihom_map_hom_injective {k G : Type} [CommRing k] [Group G] (R : Rep k G) {X Y : Rep k G} (φ : X ⟶ Y) (hφ : Function.Injective φ.hom) : Function.Injective ((ihom R).map φ).hom := by
  intro x x' h
  have h' : ∀ r : R, (show R →ₗ[k] Y from ((ihom R).map φ).hom x) r = (show R →ₗ[k] Y from ((ihom R).map φ).hom x') r := fun r => by rw [h]
  apply LinearMap.ext
  intro r
  apply hφ
  rw [← Rep.ihom_map_hom_apply_apply, ← Rep.ihom_map_hom_apply_apply]
  apply h' r

private lemma Rep.ihom_map_hom_surjective {k G : Type} [CommRing k] [Group G] (V : Type) [AddCommGroup V] [Module k V] [Module.Projective k V] (ρ : Representation k G V) {X Y : Rep k G} (φ : X ⟶ Y) (hφ : Function.Surjective φ.hom) : Function.Surjective ((ihom (Rep.of ρ)).map φ).hom := by
  intro y
  obtain ⟨h, hh⟩ := Module.projective_lifting_property φ.hom.toLinearMap (show V →ₗ[k] Y from y) hφ
  refine ⟨(show (ihom (Rep.of ρ)).obj X from h), ?_⟩
  apply LinearMap.ext
  intro r
  rw [Rep.ihom_map_hom_apply_apply]
  apply LinearMap.congr_fun hh r

private lemma Rep.ihom_map_hom_apply_eq_zero_iff {k G : Type} [CommRing k] [Group G] (R : Rep k G) {X : ShortComplex (Rep k G)} (hf : Function.Injective X.f.hom) (hfg : ∀ y : X.X₂, X.g.hom y = 0 ↔ y ∈ Set.range X.f.hom) (h : (ihom R).obj X.X₂) : ((ihom R).map X.g).hom h = 0 ↔ h ∈ Set.range ((ihom R).map X.f).hom := by
  constructor
  ·
    intro h0
    have hr (r : R) : (show R →ₗ[k] X.X₂ from h) r ∈ Set.range X.f.hom := by
      rw [← hfg, ← Rep.ihom_map_hom_apply_apply R X.g h r, h0]
      rfl
    choose s hs using hr
    have hadd (r r' : R) : s (r + r') = s r + s r' := hf (by rw [map_add, hs, hs, hs, map_add])
    have hsmul (c : k) (r : R) : s (c • r) = RingHom.id k c • s r := hf (by rw [RingHom.id_apply, map_smul, hs, hs, map_smul])
    let h' : R →ₗ[k] X.X₁ := { toFun := s, map_add' := hadd, map_smul' := hsmul }
    refine ⟨(show (ihom R).obj X.X₁ from h'), ?_⟩
    apply LinearMap.ext
    intro r
    rw [Rep.ihom_map_hom_apply_apply]
    apply hs r
  ·
    rintro ⟨h', rfl⟩
    apply LinearMap.ext
    intro r
    rw [Rep.ihom_map_hom_apply_apply, Rep.ihom_map_hom_apply_apply]
    refine (hfg _).2 ⟨_, rfl⟩

/--
[Rep_shortExact_map_ihom_of_free](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_shortExact_map_ihom_of_free.lean)
-/
@[path]
private lemma main
  {G : Type} [Group G]
  (V : Type) [AddCommGroup V] [Module.Free ℤ V]
  (ρ : Representation ℤ G V) {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact) :
  -- imply
  (X.map (ihom (Rep.of ρ))).ShortExact := by
  -- proof
  have hf : Function.Injective X.f.hom := (Rep.mono_iff_injective _).1 hX.mono_f
  apply Rep.shortExact_of_hom₄ (Rep.ihom_map_hom_injective (Rep.of ρ) X.f hf) (Rep.ihom_map_hom_surjective V ρ X.g ((Rep.epi_iff_surjective _).1 hX.epi_g)) (Rep.ihom_map_hom_apply_eq_zero_iff (Rep.of ρ) hf (Rep.apply_eq_zero_iff_of_shortExact hX))


-- created on 2026-10-20

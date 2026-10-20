import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_existsUnique_forall_specMap_comp_eq_of_flat_of_forall_exists_comap_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_existsUnique_forall_specMap_comp_eq_of_flat_of_forall_exists_comap_eq.lean)
-/
@[path]
private lemma main
    {B : Type u} [CommRing B] {ι : Type u} [Finite ι]
    (B' : ι → Type u) [∀ i, CommRing (B' i)] [∀ i, Algebra B (B' i)] [∀ i, Module.Flat B (B' i)]
    (hcov : ∀ 𝔭 : PrimeSpectrum B, ∃ (i : ι) (𝔮 : PrimeSpectrum (B' i)), PrimeSpectrum.comap (algebraMap B (B' i)) 𝔮 = 𝔭)
    {T : Scheme.{u}} (φ' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ T)
    (h : ∀ i j, Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B' i →+* B' i ⊗[B] B' j)) ≫ φ' i =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B' j →ₐ[B] B' i ⊗[B] B' j).toRingHom) ≫ φ' j) :
    ∃! φ : Spec (CommRingCat.of B) ⟶ T, ∀ i, Spec.map (CommRingCat.ofHom (algebraMap B (B' i))) ≫ φ = φ' i := by
  let π : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ Spec (CommRingCat.of B) :=
    fun i => Spec.map (CommRingCat.ofHom (algebraMap B (B' i)))
  have hflat : ∀ i, Flat (π i) := fun i => by
    rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    infer_instance
  let 𝒰 : (Spec (CommRingCat.of B)).Cover (Scheme.precoverage @Flat) :=
    Scheme.Cover.mkOfCovers ι (fun i => Spec (CommRingCat.of (B' i))) π
      (fun x => by
        obtain ⟨i, 𝔮, h𝔮⟩ := hcov x
        exact ⟨i, 𝔮, h𝔮⟩)
      hflat
  let _ : Finite 𝒰.I₀ := ‹Finite ι›
  let _ : ∀ i : 𝒰.I₀, QuasiCompact (𝒰.f i) := fun i => (inferInstance : QuasiCompact (π i))
  let _ : QuasiCompactCover 𝒰.toPreZeroHypercover := QuasiCompactCover.of_finite
  have hmem := Scheme.Cover.mem_propQCTopology 𝒰
  have hsheaf : Presieve.IsSheafFor (yoneda.obj T) (Presieve.ofArrows 𝒰.X 𝒰.f) :=
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := Scheme.fpqcTopology) (yoneda.obj T)).isSheafFor _ hmem
  rw [Presieve.isSheafFor_arrows_iff] at hsheaf
  have hcompat : Presieve.Arrows.Compatible (yoneda.obj T) 𝒰.f φ' := by
    intro i j Z gi gj hg
    simp only [yoneda_obj_map, Quiver.Hom.unop_op]
    show gi ≫ φ' i = gj ≫ φ' j
    have e1 : gi = pullback.lift gi gj hg ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
    have e2 : gj = pullback.lift gi gj hg ≫ pullback.snd _ _ := (pullback.lift_snd _ _ _).symm
    have key : pullback.fst (𝒰.f i) (𝒰.f j) ≫ φ' i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ φ' j := by
      show pullback.fst (π i) (π j) ≫ φ' i = pullback.snd (π i) (π j) ≫ φ' j
      rw [← pullbackSpecIso_hom_fst B (B' i) (B' j), ← pullbackSpecIso_hom_snd B (B' i) (B' j),
        Category.assoc, Category.assoc, h i j]
      rfl
    calc gi ≫ φ' i = (pullback.lift gi gj hg ≫ pullback.fst _ _) ≫ φ' i := by rw [← e1]
      _ = pullback.lift gi gj hg ≫ (pullback.snd _ _ ≫ φ' j) := by rw [Category.assoc, key]
      _ = gj ≫ φ' j := by rw [← Category.assoc, ← e2]
  obtain ⟨φ, hφ, huniq⟩ := hsheaf φ' hcompat
  refine ⟨φ, fun i => ?_, fun ψ hψ => huniq ψ fun i => ?_⟩
  · have h__af := hφ i
    simp only [yoneda_obj_map, Quiver.Hom.unop_op] at h__af
    exact h__af
  · simp only [yoneda_obj_map, Quiver.Hom.unop_op]
    exact hψ i

-- created on 2026-10-20

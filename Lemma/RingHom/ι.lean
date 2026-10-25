import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

universe u

private lemma CAux.surjective_specMap
  {R S : Type u} [CommRing R] [CommRing S]
  (f : RingHom R S)
  (hf : Function.Surjective f)
  (hnil : ∀ x ∈ RingHom.ker f, IsNilpotent x) :
  Surjective (Spec.map (CommRingCat.ofHom f)) := by
  refine ⟨fun x => ?_⟩
  have hx : x ∈ Set.range (PrimeSpectrum.comap f) := by
    rw [range_comap_of_surjective _ f hf]
    refine (PrimeSpectrum.mem_zeroLocus x _).mpr ?_
    intro t ht
    obtain ⟨n, hn⟩ := hnil t ht
    exact x.2.mem_of_pow_mem n (hn ▸ x.asIdeal.zero_mem)
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy⟩
/--
[AlgebraicGeometry_exists_comp_openInclusion_eq_openInclusion_comp_of_local_lift](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_comp_openInclusion_eq_openInclusion_comp_of_local_lift.lean)
-/
@[path]
private lemma main
  {T' T : Type u} [CommRing T'] [CommRing T] (π : RingHom T' T) (hπ : Function.Surjective π)
  (hker : IsNilpotent (RingHom.ker π))
  {A₀ X₀ Y Z : (Scheme : Type (u + 1))}
  (U : A₀.Opens) (g : (U : (Scheme : Type (u + 1))) ⟶ Y)
  (O : A₀.Opens → Y.Opens) (hO : ∀ W : A₀.Opens, ((TopologicalSpace.Opens.map g.base).obj (O W)) = ((TopologicalSpace.Opens.map U.ι.base).obj W))
  (fX₀ : X₀ ⟶ Spec (CommRingCat.of T))
  (V : X₀.Opens) (gZ : (V : (Scheme : Type (u + 1))) ⟶ Z) (qZ : Z ⟶ Spec (CommRingCat.of T'))
  (hgZ : IsPullback gZ (V.ι ≫ fX₀) qZ (Spec.map (CommRingCat.ofHom π)))
  (OX : X₀.Opens → Z.Opens) (hOX : ∀ W : X₀.Opens, ((TopologicalSpace.Opens.map gZ.base).obj (OX W)) = ((TopologicalSpace.Opens.map V.ι.base).obj W))
  (h₀ : X₀ ⟶ A₀) (hV : V ≤ ((TopologicalSpace.Opens.map h₀.base).obj U))
  (hZ : Z ⟶ Y) (hhZg : gZ ≫ hZ = X₀.homOfLE hV ≫ morphismRestrict h₀ U ≫ g)
  (WX : X₀.Opens) (WA : A₀.Opens) (hWW : WX ≤ ((TopologicalSpace.Opens.map h₀.base).obj WA)) :
  ∃ η : (↑(OX WX) : (Scheme : Type (u + 1))) ⟶ ↑(O WA), η ≫ (O WA).ι = (OX WX).ι ≫ hZ := by
  classical
  let _ : Surjective (Spec.map (CommRingCat.ofHom π)) := by
    refine CAux.surjective_specMap π hπ (fun x hx => ?_)
    obtain ⟨n, hn⟩ := hker
    refine ⟨n, ?_⟩
    have hx' : x ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at hx'
    exact (Submodule.mem_bot _).mp hx'
  let _ : Surjective gZ := MorphismProperty.of_isPullback hgZ.flip inferInstance
  have hrange : Set.range ((OX WX).ι ≫ hZ).base ⊆ Set.range (O WA).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    obtain ⟨v, hv⟩ := gZ.surjective ((OX WX).ι.base z)
    have hvW : v ∈ (((TopologicalSpace.Opens.map gZ.base).obj (OX WX)) : Set _) := by
      show gZ.base v ∈ (OX WX : Set Z)
      rw [hv, ← Scheme.Opens.range_ι (OX WX)]; exact ⟨z, rfl⟩
    rw [hOX] at hvW
    have h1 : ((OX WX).ι ≫ hZ).base z = hZ.base (gZ.base v) := by
      rw [Scheme.Hom.comp_base, TopCat.comp_app, hv]
    rw [h1, ← TopCat.comp_app, ← Scheme.Hom.comp_base, hhZg]
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
    have h2 : (X₀.homOfLE hV ≫ morphismRestrict h₀ U).base v ∈ (((TopologicalSpace.Opens.map g.base).obj (O WA)) : Set _) := by
      rw [hO]
      show ((X₀.homOfLE hV ≫ morphismRestrict h₀ U) ≫ U.ι).base v ∈ (WA : Set A₀)
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.comp_base,
        TopCat.comp_app]
      exact hWW hvW
    simpa [Scheme.Hom.comp_base] using h2
  refine ⟨IsOpenImmersion.lift (O WA).ι ((OX WX).ι ≫ hZ) hrange, IsOpenImmersion.lift_fac _ _ _⟩

-- created on 2026-10-20

import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma formallyUnramified
  {X Y : (Scheme : Type (u + 1))}
  (f : X ⟶ Y)
  -- given
  (hlift : ∀ (R S : Type u) [CommRing R] [CommRing S] (φ : RingHom R S), Function.Surjective φ → RingHom.ker φ ^ 2 = ⊥ → ∀ (a : Spec (CommRingCat.of S) ⟶ X) (b : Spec (CommRingCat.of R) ⟶ Y), a ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ b → ∃! l : Spec (CommRingCat.of R) ⟶ X, Spec.map (CommRingCat.ofHom φ) ≫ l = a ∧ l ≫ f = b) :
  -- imply
  FormallyUnramified f := by
  -- proof
  refine FormallyUnramified.of_hom_ext f fun R S φ hφ hker g₁ g₂ h₁ h₂ => ?_
  obtain ⟨l, -, huniq⟩ := hlift R S φ.hom hφ hker (Spec.map φ ≫ g₁) (g₁ ≫ f)
    (by simp only [CommRingCat.ofHom_hom, Category.assoc])
  apply (huniq g₁ ⟨by simp only [CommRingCat.ofHom_hom], rfl⟩).trans
    (huniq g₂ ⟨by simp only [CommRingCat.ofHom_hom, h₁], h₂.symm⟩).symm

private lemma range_subset_of_comp
  {R S : Type u} [CommRing R] [CommRing S]
  {X : (Scheme : Type (u + 1))}
  (φ : RingHom R S)
  (l : Spec (CommRingCat.of R) ⟶ X)
  (V : X.Opens)
  -- given
  (hφ : Function.Surjective φ)
  (hker : RingHom.ker φ ^ 2 = ⊥)
  (h : Set.range (Spec.map (CommRingCat.ofHom φ) ≫ l) ⊆ (V : Set X)) :
  -- imply
  Set.range l ⊆ (V : Set X) := by
  -- proof
  rintro _ ⟨p, rfl⟩
  have hmem : (p : PrimeSpectrum R) ∈ PrimeSpectrum.zeroLocus ((RingHom.ker φ : Ideal R) : Set R) := by
    intro r hr
    have h2 : r ^ 2 ∈ RingHom.ker φ ^ 2 := Ideal.pow_mem_pow hr 2
    rw [hker, Ideal.mem_bot] at h2
    apply p.2.mem_of_pow_mem 2
    ·
      rw [h2]
      apply Ideal.zero_mem _
  have hp : (p : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap φ) := by
    rw [range_comap_of_surjective _ φ hφ]
    apply hmem
  obtain ⟨q, hq⟩ := hp
  refine h ⟨q, ?_⟩
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply]
  congr 1

private lemma formallySmooth_appLE
  {X Y : (Scheme : Type (u + 1))}
  (f : X ⟶ Y)
  {U : Y.Opens}
  {V : X.Opens}
  (e : V ≤ (TopologicalSpace.Opens.map f.base).obj U)
  -- given
  (hlift : ∀ (R S : Type u) [CommRing R] [CommRing S] (φ : RingHom R S), Function.Surjective φ → RingHom.ker φ ^ 2 = ⊥ → ∀ (a : Spec (CommRingCat.of S) ⟶ X) (b : Spec (CommRingCat.of R) ⟶ Y), a ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ b → ∃! l : Spec (CommRingCat.of R) ⟶ X, Spec.map (CommRingCat.ofHom φ) ≫ l = a ∧ l ≫ f = b)
  (hU : IsAffineOpen U)
  (hV : IsAffineOpen V) :
  -- imply
  let _ := (f.appLE U V e).hom.toAlgebra
  Algebra.FormallySmooth (Y.presheaf.obj (op U)) (X.presheaf.obj (op V)) := by
  -- proof
  let _ := (f.appLE U V e).hom.toAlgebra
  refine Algebra.FormallySmooth.of_comp_surjective fun B _ _ I hI g => ?_
  let φ : RingHom B (B ⧸ I) := Ideal.Quotient.mk I
  have hφ : Function.Surjective φ := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker φ ^ 2 = ⊥ := by
    simpa [φ, Ideal.mk_ker] using hI
  let a : Spec (CommRingCat.of (B ⧸ I)) ⟶ X := Spec.map (CommRingCat.ofHom g.toRingHom) ≫ hV.fromSpec
  let b : Spec (CommRingCat.of B) ⟶ Y := Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.obj (op U)) B)) ≫ hU.fromSpec
  have hsq : a ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ b := by
    simp only [a, b, Category.assoc]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    rw [← CommRingCat.ofHom_comp]
    change f.appLE U V e ≫ CommRingCat.ofHom g.toRingHom = _
    have hg : g.toRingHom.comp (f.appLE U V e).hom = algebraMap (Y.presheaf.obj (op U)) (B ⧸ I) := by
      have := g.comp_algebraMap
      simpa [RingHom.algebraMap_toAlgebra] using this
    ext x
    ·
      change g.toRingHom ((f.appLE U V e).hom x) = φ (algebraMap (Y.presheaf.obj (op U)) B x)
      rw [← RingHom.comp_apply, hg]
      rfl
  obtain ⟨l, ⟨hl₁, hl₂⟩, -⟩ := hlift B (B ⧸ I) φ hφ hker a b hsq
  have hrange : Set.range l ⊆ Set.range hV.fromSpec := by
    rw [IsAffineOpen.range_fromSpec]
    refine range_subset_of_comp φ l V hφ hker ?_
    rw [hl₁]
    rintro _ ⟨p, rfl⟩
    have : (a p) ∈ Set.range hV.fromSpec := ⟨_, rfl⟩
    rwa [IsAffineOpen.range_fromSpec] at this
  let l' : Spec (CommRingCat.of B) ⟶ Spec (X.presheaf.obj (op V)) := IsOpenImmersion.lift hV.fromSpec l hrange
  have hl' : l' ≫ hV.fromSpec = l := IsOpenImmersion.lift_fac _ _ _
  let ψ : (X.presheaf.obj (op V)) ⟶ CommRingCat.of B := Spec.preimage l'
  have hψ : Spec.map ψ = l' := Spec.map_preimage l'
  have hcomm : ψ.hom.comp (f.appLE U V e).hom = algebraMap (Y.presheaf.obj (op U)) B := by
    have h1 : Spec.map (f.appLE U V e ≫ ψ) ≫ hU.fromSpec = Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.obj (op U)) B)) ≫ hU.fromSpec := by
      rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e, hψ, ← Category.assoc, hl']
      apply hl₂
    rw [cancel_mono] at h1
    apply congrArg (fun t => t.hom) (Spec.map_injective h1)
  have hliftg : φ.comp ψ.hom = g.toRingHom := by
    have h1 : Spec.map (ψ ≫ CommRingCat.ofHom φ) ≫ hV.fromSpec = Spec.map (CommRingCat.ofHom g.toRingHom) ≫ hV.fromSpec := by
      rw [Spec.map_comp, Category.assoc, hψ, hl']
      apply hl₁
    rw [cancel_mono] at h1
    apply congrArg (fun t => t.hom) (Spec.map_injective h1)
  refine ⟨⟨ψ.hom, fun r => ?_⟩, ?_⟩
  ·
    change ψ.hom ((f.appLE U V e).hom r) = algebraMap (Y.presheaf.obj (op U)) B r
    rw [← RingHom.comp_apply, hcomm]
  ·
    apply AlgHom.ext
    intro x
    change φ (ψ.hom x) = g x
    rw [← RingHom.comp_apply, hliftg]
    rfl

private lemma etale
  {X Y : (Scheme : Type (u + 1))}
  (f : X ⟶ Y) [LocallyOfFinitePresentation f]
  -- given
  (hlift : ∀ (R S : Type u) [CommRing R] [CommRing S] (φ : RingHom R S), Function.Surjective φ → RingHom.ker φ ^ 2 = ⊥ → ∀ (a : Spec (CommRingCat.of S) ⟶ X) (b : Spec (CommRingCat.of R) ⟶ Y), a ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ b → ∃! l : Spec (CommRingCat.of R) ⟶ X, Spec.map (CommRingCat.ofHom φ) ≫ l = a ∧ l ≫ f = b) :
  -- imply
  Etale f := by
  -- proof
  have hfu : FormallyUnramified f := formallyUnramified f hlift
  refine ⟨fun {U} hU {V} hV e => ?_⟩
  have hfp := f.finitePresentation_appLE hU hV e
  have hur := f.formallyUnramified_appLE hU hV e
  have hsm := formallySmooth_appLE f e hlift hU hV
  let _ := (f.appLE U V e).hom.toAlgebra
  have : Algebra.FormallyUnramified (Y.presheaf.obj (op U)) (X.presheaf.obj (op V)) := hur
  have : Algebra.FormallySmooth (Y.presheaf.obj (op U)) (X.presheaf.obj (op V)) := hsm
  have : Algebra.FinitePresentation (Y.presheaf.obj (op U)) (X.presheaf.obj (op V)) := hfp
  have : Algebra.FormallyEtale (Y.presheaf.obj (op U)) (X.presheaf.obj (op V)) :=
    Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth
  refine (⟨this, ‹_›⟩ : Algebra.Etale (Y.presheaf.obj (op U)) (X.presheaf.obj (op V)))

/--
[AlgebraicGeometry_Etale_of_forall_existsUnique_lift](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Etale_of_forall_existsUnique_lift.lean)
-/
@[path]
private lemma main
  {X Y : (Scheme : Type (u + 1))}
  (f : X ⟶ Y) [LocallyOfFinitePresentation f]
  -- given
  (hlift : ∀ (R S : Type u) [CommRing R] [CommRing S] (φ : RingHom R S), Function.Surjective φ → RingHom.ker φ ^ 2 = ⊥ → ∀ (a : Spec (CommRingCat.of S) ⟶ X) (b : Spec (CommRingCat.of R) ⟶ Y), a ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ b → ∃! l : Spec (CommRingCat.of R) ⟶ X, Spec.map (CommRingCat.ofHom φ) ≫ l = a ∧ l ≫ f = b) :
  -- imply
  Etale f :=
  etale f hlift


-- created on 2026-10-20

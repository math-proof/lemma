import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_Scheme_Hom_eq_of_forall_spec_comp_eq_of_isFinite_of_isArtinianRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_eq_of_forall_spec_comp_eq_of_isFinite_of_isArtinianRing.lean)
-/
@[path]
private lemma main
  {T : Type} [CommRing T] [IsArtinianRing T] {Z Y : Scheme} (p : Z ⟶ Spec (CommRingCat.of T)) [IsFinite p]
  (g h : Z ⟶ Y)
  (H : ∀ (B : Type) [CommRing B] [IsArtinianRing B] [IsLocalRing B] (z : Spec (CommRingCat.of B) ⟶ Z), z ≫ g = z ≫ h) :
  g = h := by
  classical
  have hfin := (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp ‹IsFinite p›
  let _ : IsAffine Z := hfin.1
  let _ : IsArtinianRing ↑((Spec (CommRingCat.of T)).presheaf.obj (Opposite.op (⊤ : (Spec (CommRingCat.of T)).Opens))) :=
    (Scheme.ΓSpecIso (CommRingCat.of T)).commRingCatIsoToRingEquiv.symm.surjective.isArtinianRing
  let _ : IsArtinianRing ↑(Z.presheaf.obj (Opposite.op (⊤ : Z.Opens))) := by
    let _ : Algebra ↑((Spec (CommRingCat.of T)).presheaf.obj (Opposite.op (⊤ : (Spec (CommRingCat.of T)).Opens))) ↑(Z.presheaf.obj (Opposite.op (⊤ : Z.Opens))) := p.appTop.hom.toAlgebra
    let _ : Module.Finite ↑((Spec (CommRingCat.of T)).presheaf.obj (Opposite.op (⊤ : (Spec (CommRingCat.of T)).Opens))) ↑(Z.presheaf.obj (Opposite.op (⊤ : Z.Opens))) := hfin.2
    apply IsArtinianRing.of_finite
      ↑((Spec (CommRingCat.of T)).presheaf.obj (Opposite.op (⊤ : (Spec (CommRingCat.of T)).Opens)))
      ↑(Z.presheaf.obj (Opposite.op (⊤ : Z.Opens)))
  let _ : IsLocallyArtinian Z := IsLocallyArtinian.of_isImmersion Z.isoSpec.hom
  apply Scheme.hom_ext_of_forall
  intro z
  let _ : IsLocallyArtinian (Spec (Z.presheaf.obj (Opposite.op (⊤ : Z.Opens)))) := inferInstance
  have hclopen : IsClopen ({Z.toSpecΓ.base z} : Set ↥(Spec (Z.presheaf.obj (Opposite.op (⊤ : Z.Opens))))) :=
    ⟨isClosed_discrete _, isOpen_discrete _⟩
  obtain ⟨e, -, he⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hclopen
  have hUset : (Z.basicOpen e : Set Z) = {z} := by
    ext w
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    show Z.toSpecΓ.base w ∈ (PrimeSpectrum.basicOpen e : TopologicalSpace.Opens (PrimeSpectrum ↑(Z.presheaf.obj (Opposite.op (⊤ : Z.Opens))))) ↔
      w ∈ ({z} : Set Z)
    have : Z.toSpecΓ.base w ∈ (PrimeSpectrum.basicOpen e : TopologicalSpace.Opens (PrimeSpectrum ↑(Z.presheaf.obj (Opposite.op (⊤ : Z.Opens))))) ↔
        Z.toSpecΓ.base w ∈ (↑(PrimeSpectrum.basicOpen e) : Set (PrimeSpectrum ↑(Z.presheaf.obj (Opposite.op (⊤ : Z.Opens))))) := Iff.rfl
    rw [this, ← he]
    constructor
    ·
      intro hw
      apply (Scheme.homeoOfIso Z.isoSpec).injective (Set.eq_of_mem_singleton hw)
    ·
      intro hw
      rw [Set.eq_of_mem_singleton hw]
      apply Set.mem_singleton
  have hU : IsAffineOpen (Z.basicOpen e) := (isAffineOpen_top Z).basicOpen e
  have hzmem : z ∈ Z.basicOpen e := by
    rw [← SetLike.mem_coe, hUset]
    rfl
  refine ⟨Z.basicOpen e, hzmem, ?_⟩
  let _ : IsArtinianRing ↑(Z.presheaf.obj (Opposite.op (Z.basicOpen e))) := by
    let _ : IsArtinianRing ↑((Z.basicOpen e).toScheme.presheaf.obj (Opposite.op (⊤ : (Z.basicOpen e).toScheme.Opens))) := IsLocallyArtinian.isArtinianRing_of_isAffine
    apply (Z.basicOpen e).topIso.commRingCatIsoToRingEquiv.surjective.isArtinianRing
  let _ : IsLocalRing ↑(Z.presheaf.obj (Opposite.op (Z.basicOpen e))) := by
    have hsub : Subsingleton ↥(Spec (Z.presheaf.obj (Opposite.op (Z.basicOpen e)))) := by
      refine ⟨fun a b => (Scheme.homeoOfIso hU.isoSpec.symm).injective ?_⟩
      apply Subtype.ext
      have ha := ((Scheme.homeoOfIso hU.isoSpec.symm) a).2
      have hb := ((Scheme.homeoOfIso hU.isoSpec.symm) b).2
      rw [← SetLike.mem_coe, hUset] at ha hb
      apply ha.trans hb.symm
    have hne : Nonempty ↥(Spec (Z.presheaf.obj (Opposite.op (Z.basicOpen e)))) :=
      ⟨Scheme.homeoOfIso hU.isoSpec ⟨z, hzmem⟩⟩
    let _ : Nontrivial ↑(Z.presheaf.obj (Opposite.op (Z.basicOpen e))) := PrimeSpectrum.nonempty_iff_nontrivial.mp hne
    obtain ⟨M, hM⟩ := Ideal.exists_maximal ↑(Z.presheaf.obj (Opposite.op (Z.basicOpen e)))
    refine IsLocalRing.of_unique_max_ideal ⟨M, hM, fun J hJ => ?_⟩
    have := hsub.elim (⟨J, hJ.isPrime⟩ : PrimeSpectrum ↑(Z.presheaf.obj (Opposite.op (Z.basicOpen e)))) ⟨M, hM.isPrime⟩
    apply congrArg PrimeSpectrum.asIdeal this
  have key := H ↑(Z.presheaf.obj (Opposite.op (Z.basicOpen e))) hU.fromSpec
  rw [← hU.isoSpec_inv_ι, Category.assoc, Category.assoc] at key
  apply (cancel_epi hU.isoSpec.inv).1 key


-- created on 2026-10-20

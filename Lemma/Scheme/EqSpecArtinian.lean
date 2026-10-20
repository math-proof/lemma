import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

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
  let _ : IsArtinianRing ↑Γ(Spec (CommRingCat.of T), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of T)).commRingCatIsoToRingEquiv.symm.surjective.isArtinianRing
  let _ : IsArtinianRing ↑Γ(Z, ⊤) := by
    let _ : Algebra ↑Γ(Spec (CommRingCat.of T), ⊤) ↑Γ(Z, ⊤) := p.appTop.hom.toAlgebra
    let _ : Module.Finite ↑Γ(Spec (CommRingCat.of T), ⊤) ↑Γ(Z, ⊤) := hfin.2
    exact IsArtinianRing.of_finite ↑Γ(Spec (CommRingCat.of T), ⊤) ↑Γ(Z, ⊤)
  let _ : IsLocallyArtinian Z := IsLocallyArtinian.of_isImmersion Z.isoSpec.hom
  apply Scheme.hom_ext_of_forall
  intro z
  let _ : IsLocallyArtinian (Spec Γ(Z, ⊤)) := inferInstance
  have hclopen : IsClopen ({Z.toSpecΓ.base z} : Set ↥(Spec Γ(Z, ⊤))) :=
    ⟨isClosed_discrete _, isOpen_discrete _⟩
  obtain ⟨e, -, he⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hclopen
  have hUset : (Z.basicOpen e : Set Z) = {z} := by
    ext w
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    show Z.toSpecΓ.base w ∈ (PrimeSpectrum.basicOpen e : TopologicalSpace.Opens (PrimeSpectrum ↑Γ(Z, ⊤))) ↔
      w ∈ ({z} : Set Z)
    have : Z.toSpecΓ.base w ∈ (PrimeSpectrum.basicOpen e : TopologicalSpace.Opens (PrimeSpectrum ↑Γ(Z, ⊤))) ↔
        Z.toSpecΓ.base w ∈ (↑(PrimeSpectrum.basicOpen e) : Set (PrimeSpectrum ↑Γ(Z, ⊤))) := Iff.rfl
    rw [this, ← he]
    constructor
    · intro hw
      exact (Scheme.homeoOfIso Z.isoSpec).injective (Set.eq_of_mem_singleton hw)
    · intro hw
      rw [Set.eq_of_mem_singleton hw]
      exact Set.mem_singleton _
  have hU : IsAffineOpen (Z.basicOpen e) := (isAffineOpen_top Z).basicOpen e
  refine ⟨Z.basicOpen e, by rw [← SetLike.mem_coe, hUset]; rfl, ?_⟩
  let _ : IsArtinianRing ↑Γ(Z, Z.basicOpen e) := by
    let _ : IsArtinianRing ↑Γ(↑(Z.basicOpen e), ⊤) := IsLocallyArtinian.isArtinianRing_of_isAffine
    exact (Z.basicOpen e).topIso.commRingCatIsoToRingEquiv.surjective.isArtinianRing
  let _ : IsLocalRing ↑Γ(Z, Z.basicOpen e) := by
    have hsub : Subsingleton ↥(Spec Γ(Z, Z.basicOpen e)) := by
      refine ⟨fun a b => (Scheme.homeoOfIso hU.isoSpec.symm).injective ?_⟩
      apply Subtype.ext
      have ha := ((Scheme.homeoOfIso hU.isoSpec.symm) a).2
      have hb := ((Scheme.homeoOfIso hU.isoSpec.symm) b).2
      rw [← SetLike.mem_coe, hUset] at ha hb
      exact ha.trans hb.symm
    have hne : Nonempty ↥(Spec Γ(Z, Z.basicOpen e)) :=
      ⟨Scheme.homeoOfIso hU.isoSpec ⟨z, by rw [← SetLike.mem_coe, hUset]; rfl⟩⟩
    let _ : Nontrivial ↑Γ(Z, Z.basicOpen e) := PrimeSpectrum.nonempty_iff_nontrivial.mp hne
    obtain ⟨M, hM⟩ := Ideal.exists_maximal ↑Γ(Z, Z.basicOpen e)
    refine IsLocalRing.of_unique_max_ideal ⟨M, hM, fun J hJ => ?_⟩
    have := hsub.elim (⟨J, hJ.isPrime⟩ : PrimeSpectrum ↑Γ(Z, Z.basicOpen e)) ⟨M, hM.isPrime⟩
    exact congrArg PrimeSpectrum.asIdeal this
  have key := H ↑Γ(Z, Z.basicOpen e) hU.fromSpec
  rw [← hU.isoSpec_inv_ι, Category.assoc, Category.assoc] at key
  exact (cancel_epi hU.isoSpec.inv).1 key


-- created on 2026-10-20

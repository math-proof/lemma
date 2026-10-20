import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma natCard_primeSpectrum_le_finrank
  (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A]
  [Module.Finite k A] :
  Nat.card (PrimeSpectrum A) ≤ Module.finrank k A := by
  classical
  let _ : IsArtinianRing A := IsArtinianRing.of_finite k A
  let _ : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  let e : (A ⧸ nilradical A) ≃ₗ[k] ((I : MaximalSpectrum A) → A ⧸ I.asIdeal) :=
    (IsArtinianRing.quotNilradicalEquivPi A).toLinearEquiv.restrictScalars k
  have h1 : ∀ I : MaximalSpectrum A, 1 ≤ Module.finrank k (A ⧸ I.asIdeal) := fun I => by
    let _ := I.isMaximal
    let _ := Ideal.Quotient.field I.asIdeal
    apply Module.finrank_pos
  calc
    _ = Nat.card (MaximalSpectrum A) := Nat.card_congr IsArtinianRing.primeSpectrumEquivMaximalSpectrum
    _ = ∑ _ : MaximalSpectrum A, 1 := by
      rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Nat.card_eq_fintype_card]
    _ ≤ ∑ I : MaximalSpectrum A, Module.finrank k (A ⧸ I.asIdeal) := Finset.sum_le_sum fun I _ => h1 I
    _ = Module.finrank k ((I : MaximalSpectrum A) → A ⧸ I.asIdeal) := (Module.finrank_pi_fintype k).symm
    _ = Module.finrank k (A ⧸ nilradical A) := e.finrank_eq.symm
    _ = Module.finrank k (A ⧸ (nilradical A).restrictScalars k) :=
      (Submodule.Quotient.restrictScalarsEquiv k (nilradical A)).finrank_eq.symm
    _ ≤ Module.finrank k A := Submodule.finrank_quotient_le ((nilradical A).restrictScalars k)
/--
[AlgebraicGeometry_Scheme_Hom_natCard_le_finrank_of_isFinite](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_natCard_le_finrank_of_isFinite.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k] {Z : (Scheme : Type (u + 1))} (z : Z ⟶ Spec (CommRingCat.of k)) [IsFinite z]
  (t : Spec (CommRingCat.of k)) :
  Nat.card Z ≤ Scheme.Hom.finrank z t := by
  classical
  obtain ⟨hZaff, hfinTop⟩ := (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp (inferInstance : IsFinite z)
  let _ : IsAffine Z := hZaff
  let φ : CommRingCat.of k ⟶ (Z.presheaf.obj (Opposite.op (⊤ : Z.Opens))) := (Scheme.ΓSpecIso (.of k)).inv ≫ z.appTop
  have hφfin : φ.hom.Finite :=
    RingHom.Finite.comp hfinTop
      (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).surjective)
  have hφflat : φ.hom.Flat := by
    let _ := φ.hom.toAlgebra
    refine (inferInstance : Module.Flat k (Z.presheaf.obj (Opposite.op (⊤ : Z.Opens))))
  have hfac : z = Z.isoSpec.hom ≫ Spec.map φ := by
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, Scheme.isoSpec_hom_naturality_assoc,
      Iso.hom_inv_id, Category.comp_id]
  let _ : IsFinite (Spec.map φ) := (IsFinite.SpecMap_iff φ).2 hφfin
  let _ : Flat (Spec.map φ) := Flat.SpecMap_iff.2 hφflat
  rw [hfac, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_eq_finrank hφfin hφflat]
  let _ : Algebra k (Z.presheaf.obj (Opposite.op (⊤ : Z.Opens))) := φ.hom.toAlgebra
  let _ : Module.Finite k (Z.presheaf.obj (Opposite.op (⊤ : Z.Opens))) := hφfin
  simp only [RingHom.finrank, Module.rankAtStalk_eq_finrank_of_free]
  show Nat.card Z ≤ Module.finrank k (Z.presheaf.obj (Opposite.op (⊤ : Z.Opens)))
  calc
    _ = Nat.card (PrimeSpectrum (Z.presheaf.obj (Opposite.op (⊤ : Z.Opens)))) :=
      Nat.card_congr (Scheme.homeoOfIso Z.isoSpec).toEquiv
    _ ≤ Module.finrank k (Z.presheaf.obj (Opposite.op (⊤ : Z.Opens))) :=
      natCard_primeSpectrum_le_finrank k (Z.presheaf.obj (Opposite.op (⊤ : Z.Opens)))


-- created on 2026-10-20

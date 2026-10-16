import Mathlib
import sympy.Basic
open scoped TensorProduct


private lemma transport
  {Sg A C C' : Type} {r' : Sg} [CommRing Sg] [CommRing A] [CommRing C] [CommRing C'] [Algebra Sg A] [IsLocalization.Away r' A] [Algebra Sg C] [Algebra C C'] [Algebra Sg C'] [IsScalarTower Sg C C'] [Algebra A C'] [IsScalarTower Sg A C'] [IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers r')) C'] [Module.Finite Sg C] [Module.Free Sg C] [Module.FaithfullyFlat Sg C] [Algebra.FinitePresentation Sg C] :
-- imply
  Module.Finite A C' ∧ Module.Free A C' ∧ Module.FaithfullyFlat A C' ∧ Algebra.FinitePresentation A C' := by
-- proof
  have hpo : Algebra.IsPushout Sg C A C' :=
    (Algebra.isLocalization_iff_isPushout (Submonoid.powers r') A).mp inferInstance
  let _ : Algebra.IsPushout Sg A C C' := hpo.symm
  have e : A ⊗[Sg] C ≃ₐ[A] C' := Algebra.IsPushout.equiv Sg A C C'
  refine ⟨Module.Finite.equiv e.toLinearEquiv, Module.Free.of_equiv e.toLinearEquiv,
    Module.FaithfullyFlat.of_linearEquiv A (A ⊗[Sg] C) e.symm.toLinearEquiv, Algebra.FinitePresentation.equiv e⟩


/--
[Algebra_exists_algebra_away_mul_finite_free_faithfullyFlat_finitePresentation_of_isLocalization_powers](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_algebra_away_mul_finite_free_faithfullyFlat_finitePresentation_of_isLocalization_powers.lean)
-/
@[path]
private lemma main
  {S : Type} [CommRing S]
  {g r : S}
  {C : Type} [CommRing C] [Algebra S C] [Algebra (Localization.Away g) C] [IsScalarTower S (Localization.Away g) C]
  {C' : Type} [CommRing C'] [Algebra S C'] [Algebra C C'] [IsScalarTower S C C'] [IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers r)) C']
-- given
  (hfin : Module.Finite (Localization.Away g) C)
  (hfree : Module.Free (Localization.Away g) C)
  (hff : Module.FaithfullyFlat (Localization.Away g) C)
  (hfp : Algebra.FinitePresentation (Localization.Away g) C) :
-- imply
  ∃ (_ : Algebra (Localization.Away (g * r)) C') (_ : IsScalarTower S (Localization.Away (g * r)) C'),
    Module.Finite (Localization.Away (g * r)) C' ∧ Module.Free (Localization.Away (g * r)) C' ∧
    Module.FaithfullyFlat (Localization.Away (g * r)) C' ∧
    Algebra.FinitePresentation (Localization.Away (g * r)) C' := by
-- proof
  classical
  let _ : Module.Finite (Localization.Away g) C := hfin
  let _ : Module.Free (Localization.Away g) C := hfree
  let _ : Module.FaithfullyFlat (Localization.Away g) C := hff
  let _ : Algebra.FinitePresentation (Localization.Away g) C := hfp
  obtain ⟨e₀⟩ : Nonempty (Localization.Away (algebraMap S (Localization.Away g) r) ≃ₐ[S] Localization.Away (g * r)) :=
    ⟨IsLocalization.algEquiv (Submonoid.powers (g * r)) _ _⟩
  let algSgA : Algebra (Localization.Away g) (Localization.Away (g * r)) :=
    (e₀.toRingEquiv.toRingHom.comp
      (algebraMap (Localization.Away g) (Localization.Away (algebraMap S (Localization.Away g) r)))).toAlgebra
  let _ : IsScalarTower S (Localization.Away g) (Localization.Away (g * r)) :=
    IsScalarTower.of_algebraMap_eq (R := S) (S := Localization.Away g) (A := Localization.Away (g * r))
      (fun s => by
        show algebraMap S (Localization.Away (g * r)) s =
          e₀ (algebraMap (Localization.Away g) (Localization.Away (algebraMap S (Localization.Away g) r))
            (algebraMap S (Localization.Away g) s))
        rw [← IsScalarTower.algebraMap_apply S (Localization.Away g)
          (Localization.Away (algebraMap S (Localization.Away g) r)) s, AlgEquiv.commutes])
  have e₁ : Localization.Away (algebraMap S (Localization.Away g) r) ≃ₐ[Localization.Away g] Localization.Away (g * r) :=
    AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) (fun _ => rfl)
  let _ : IsLocalization.Away (algebraMap S (Localization.Away g) r) (Localization.Away (g * r)) :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (algebraMap S (Localization.Away g) r)) e₁
  let _ : Algebra (Localization.Away g) C' :=
    ((algebraMap C C').comp (algebraMap (Localization.Away g) C)).toAlgebra
  let _ : IsScalarTower (Localization.Away g) C C' :=
    IsScalarTower.of_algebraMap_eq (R := Localization.Away g) (S := C) (A := C') (fun _ => rfl)
  let _ : IsScalarTower S (Localization.Away g) C' :=
    IsScalarTower.of_algebraMap_eq (R := S) (S := Localization.Away g) (A := C') (fun s => by
      show algebraMap S C' s =
        algebraMap C C' (algebraMap (Localization.Away g) C (algebraMap S (Localization.Away g) s))
      rw [← IsScalarTower.algebraMap_apply S (Localization.Away g) C s,
        ← IsScalarTower.algebraMap_apply S C C' s])
  let _ : IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers (algebraMap S (Localization.Away g) r))) C' := by
    have hsub : Algebra.algebraMapSubmonoid C (Submonoid.powers (algebraMap S (Localization.Away g) r)) =
        Algebra.algebraMapSubmonoid C (Submonoid.powers r) := by
      rw [Algebra.algebraMapSubmonoid_powers, Algebra.algebraMapSubmonoid_powers,
        ← IsScalarTower.algebraMap_apply S (Localization.Away g) C r]
    rw [hsub]
    infer_instance
  have hu : IsUnit (algebraMap S C' (g * r)) := by
    rw [map_mul]
    refine IsUnit.mul ?_ ?_
    ·
      rw [IsScalarTower.algebraMap_apply S (Localization.Away g) C' g]
      apply (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).map _
    ·
      rw [IsScalarTower.algebraMap_apply S C C' r]
      apply IsLocalization.map_units C' (⟨algebraMap S C r, Algebra.mem_algebraMapSubmonoid_of_mem (⟨r, Submonoid.mem_powers r⟩ : Submonoid.powers r)⟩ : Algebra.algebraMapSubmonoid C (Submonoid.powers r))
  let algAC' : Algebra (Localization.Away (g * r)) C' := (IsLocalization.Away.lift (g * r) hu).toAlgebra
  let tSAC' : IsScalarTower S (Localization.Away (g * r)) C' :=
    IsScalarTower.of_algebraMap_eq (R := S) (S := Localization.Away (g * r)) (A := C')
      (fun s => (IsLocalization.Away.lift_eq (g * r) hu s).symm)
  let _ : IsScalarTower (Localization.Away g) (Localization.Away (g * r)) C' := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    ext s
    show algebraMap (Localization.Away g) C' (algebraMap S (Localization.Away g) s) =
      algebraMap (Localization.Away (g * r)) C'
        (algebraMap (Localization.Away g) (Localization.Away (g * r)) (algebraMap S (Localization.Away g) s))
    rw [← IsScalarTower.algebraMap_apply S (Localization.Away g) C' s,
      ← IsScalarTower.algebraMap_apply S (Localization.Away g) (Localization.Away (g * r)) s,
      ← IsScalarTower.algebraMap_apply S (Localization.Away (g * r)) C' s]
  obtain ⟨h1, h2, h3, h4⟩ := transport (Sg := Localization.Away g) (A := Localization.Away (g * r))
    (C := C) (C' := C') (r' := algebraMap S (Localization.Away g) r)
  refine ⟨algAC', tSAC', h1, h2, h3, h4⟩


-- created on 2026-10-13

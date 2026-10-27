import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma finrank_eq_length_aux
  {k : Type u} [Field k] [IsAlgClosed k] (L : Type v) [CommRing L] [Algebra k L] [IsLocalRing L]
  [Module.Finite k L] (n : ℕ) :
  ∀ (M : Type w) [AddCommGroup M] [Module L M] [Module k M] [IsScalarTower k L M] [Module.Finite k M], Module.finrank k M = n → (Module.finrank k M : ENat) = Module.length L M := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M _ _ _ _ _ hn
    if hM : Subsingleton M then
      rw [Module.length_eq_zero, Module.finrank_zero_of_subsingleton, Nat.cast_zero]
    else
      let _ : Nontrivial M := by
        rw [← not_subsingleton_iff_nontrivial]
        apply hM
      let _ : IsArtinian L M := isArtinian_of_tower k (inferInstance : IsArtinian k M)
      let _ : WellFoundedLT (Submodule L M) :=
        ⟨(wellFounded_lt : WellFounded ((· < ·) : Submodule L M → Submodule L M → Prop))⟩
      obtain ⟨N, hNat⟩ := IsAtomic.exists_atom (Submodule L M)
      let hN : IsSimpleModule L N := by
        rw [isSimpleModule_iff_isAtom]
        apply hNat
      rw [isSimpleModule_iff_quot_maximal] at hN
      obtain ⟨I, hI, ⟨e⟩⟩ := hN
      have hIm : I = IsLocalRing.maximalIdeal L := IsLocalRing.eq_maximalIdeal hI
      have hN1 : Module.finrank k N = 1 := by
        let _ : Field (L ⧸ I) := Ideal.Quotient.field I
        let _ : Module.Finite k (L ⧸ I) :=
          Module.Finite.of_surjective (Ideal.Quotient.mkₐ k I).toLinearMap (Ideal.Quotient.mkₐ_surjective k I)
        let _ : Algebra.IsIntegral k (L ⧸ I) := Algebra.IsIntegral.of_finite k (L ⧸ I)
        have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := L ⧸ I)
        have h1 : Module.finrank k (L ⧸ I) = 1 := by
          rw [← (AlgEquiv.ofBijective (Algebra.ofId k (L ⧸ I)) hb).toLinearEquiv.finrank_eq, Module.finrank_self]
        rw [← h1]
        apply (e.restrictScalars k).finrank_eq
      have hNlen : Module.length L N = 1 := Module.length_eq_one L N
      have hq : Module.finrank k (M ⧸ N) = Module.finrank k M - Module.finrank k N := Submodule.finrank_quotient N
      have hpos : 0 < Module.finrank k M := Module.finrank_pos
      have hlt : Module.finrank k (M ⧸ N) < n := by
        rw [hq, hN1, ← hn]
        omega
      have ihq := ih _ hlt (M ⧸ N) rfl
      have hadd : Module.length L M = Module.length L N + Module.length L (M ⧸ N) :=
        Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N)
      rw [hadd, hNlen, ← ihq, hq, hN1]
      have : (Module.finrank k M : ENat) = ((1 + (Module.finrank k M - 1) : ℕ) : ENat) := by
        congr 1
        omega
      rw [this, Nat.cast_add, Nat.cast_one]
private lemma finrank_eq_length
  {k : Type u} [Field k] [IsAlgClosed k] (L : Type v) [CommRing L] [Algebra k L] [IsLocalRing L]
  [Module.Finite k L] :
  (Module.finrank k L : ENat) = Module.length L L :=
  finrank_eq_length_aux L (Module.finrank k L) L rfl
private lemma finrank_eq_sum_length_localization
  {k : Type u} [Field k] [IsAlgClosed k] (S : Type v) [CommRing S] [Algebra k S]
  [Module.Finite k S] [Fintype (PrimeSpectrum S)] :
  (Module.finrank k S : ENat) = ∑ p : PrimeSpectrum S, Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) := by
  let _ : IsArtinianRing S := isArtinian_of_tower k inferInstance
  rw [IsArtinianRing.finrank_eq_sum_primeSpectrum S k, Nat.cast_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  let _ : Module.Finite k (Localization.AtPrime p.asIdeal) :=
    Module.Finite.of_surjective (Algebra.algHom k S (Localization.AtPrime p.asIdeal)).toLinearMap
      (IsArtinianRing.localization_surjective p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal))
  apply finrank_eq_length (Localization.AtPrime p.asIdeal)
private lemma length_self_eq_of_ringEquiv
  {A : Type v} {B : Type w} [CommRing A] [CommRing B] (e : A ≃+* B) :
  Module.length A A = Module.length B B := by
  let _ : Algebra A B := e.toRingHom.toAlgebra
  have h1 : Module.length A B = Module.length B B :=
    Module.length_eq_of_surjective (S := A) (R := B) (M := B) e.surjective
  rw [← h1]
  let l : B ≃ₗ[A] A :=
    { toFun := e.symm, invFun := e, map_add' := fun x y => by simp,
      map_smul' := fun a x => by
        show e.symm (e a * x) = a * e.symm x
        rw [map_mul, RingEquiv.symm_apply_apply],
      left_inv := fun x => by simp, right_inv := fun x => by simp }
  apply (LinearEquiv.length_eq l).symm
variable {k : Type u} [Field k]
private lemma finrank_sections_eq
  {C : (Scheme : Type (u + 1))} (z : C ⟶ Spec (CommRingCat.of k)) [IsFinite z] [Flat z] [IsAffine C]
  (n : ℕ) (hrank : ∀ s : ↥(Spec (CommRingCat.of k)), z.finrank s = n) :
    let _ : Algebra k (C.presheaf.obj (op ⊤)) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
    Module.Finite k (C.presheaf.obj (op ⊤)) ∧ Module.finrank k (C.presheaf.obj (op ⊤)) = n := by
  set φ : CommRingCat.of k ⟶ (C.presheaf.obj (op ⊤)) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop with hφ
  let _ : Algebra k (C.presheaf.obj (op ⊤)) := φ.hom.toAlgebra
  have hbij : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv
  have hFin : φ.hom.Finite := by
    show (z.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).Finite
    apply z.finite_appTop.comp (RingHom.Finite.of_surjective _ hbij.surjective)
  have hFlat : φ.hom.Flat := by
    show (z.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).Flat
    apply (RingHom.Flat.of_bijective hbij).comp z.flat_appTop
  have hfin : Module.Finite k (C.presheaf.obj (op ⊤)) := hFin
  refine ⟨hfin, ?_⟩
  have hz : z = C.isoSpec.hom ≫ Spec.map φ := by
    rw [hφ, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  let _ : IsFinite (Spec.map φ) := (IsFinite.SpecMap_iff φ).2 hFin
  let _ : Flat (Spec.map φ) := Flat.SpecMap_iff.2 hFlat
  obtain ⟨s⟩ := (inferInstance : Nonempty ↥(Spec (CommRingCat.of k)))
  have h1 := hrank s
  rw [hz, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_eq_finrank hFin hFlat] at h1
  have h2 : φ.hom.finrank s = Module.finrank k (C.presheaf.obj (op ⊤)) := by
    have : φ.hom = algebraMap k (C.presheaf.obj (op ⊤)) := rfl
    rw [this, RingHom.finrank_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
    rfl
  rw [← h2, h1]
private lemma flat_of_field {C : (Scheme : Type (u + 1))} (z : C ⟶ Spec (CommRingCat.of k)) [IsFinite z] : Flat z := by
  let _ : IsAffine C := isAffine_of_isAffineHom z
  set φ : CommRingCat.of k ⟶ (C.presheaf.obj (op ⊤)) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop with hφ
  have hFlat : φ.hom.Flat := by
    let _ : Algebra k (C.presheaf.obj (op ⊤)) := φ.hom.toAlgebra
    have : Module.Flat k (C.presheaf.obj (op ⊤)) := inferInstance
    refine this
  have hz : z = C.isoSpec.hom ≫ Spec.map φ := by
    rw [hφ, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  let _ : Flat (Spec.map φ) := Flat.SpecMap_iff.2 hFlat
  rw [hz]
  infer_instance
/--
[AlgebraicGeometry_finrank_eq_finsum_length_stalk_of_isFinite_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_finrank_eq_finsum_length_stalk_of_isFinite_of_isAlgClosed.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k] [IsAlgClosed k] {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of k)) [IsFinite f]
  (s : ↥(Spec (CommRingCat.of k))) :
  (f.finrank s : ENat) = finsum (fun x : Subtype (fun x : Spec (CommRingCat.of k) ⟶ X => x ≫ f = 𝟙 (Spec (CommRingCat.of k))) => Module.length (X.presheaf.stalk (x.1.base (IsLocalRing.closedPoint k))) (X.presheaf.stalk (x.1.base (IsLocalRing.closedPoint k)))) := by
  classical
  let _ : IsAffine X := isAffine_of_isAffineHom f
  let _ : Flat f := flat_of_field f
  let _ : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain ⟨hfinS, hrank⟩ := finrank_sections_eq f (f.finrank s) (fun s' => by rw [Subsingleton.elim s' s])
  let _ : Algebra k (X.presheaf.obj (op ⊤)) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom.toAlgebra
  let _ : Module.Finite k (X.presheaf.obj (op ⊤)) := hfinS
  let _ : IsArtinianRing (X.presheaf.obj (op ⊤)) := isArtinian_of_tower k inferInstance
  let _ : Fintype (PrimeSpectrum (X.presheaf.obj (op ⊤))) := Fintype.ofFinite _
  rw [← hrank, finrank_eq_sum_length_localization (k := k) (X.presheaf.obj (op ⊤))]
  let _ : IsLocallyArtinian X := IsLocallyArtinian.of_locallyQuasiFinite f
  have hcl : closedPoints X = Set.univ := closedPoints_eq_univ
  have hU : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  let E₁ : Subtype (fun x : Spec (CommRingCat.of k) ⟶ X => x ≫ f = 𝟙 (Spec (CommRingCat.of k))) ≃ ↥(⊤ : X.Opens) :=
    (pointEquivClosedPoint f).trans
      ⟨fun x => ⟨x.1, trivial⟩, fun x => ⟨x.1, hcl.symm ▸ Set.mem_univ _⟩, fun x => rfl, fun x => rfl⟩
  let E₂ : ↥(⊤ : X.Opens) ≃ PrimeSpectrum (X.presheaf.obj (op ⊤)) := (Scheme.homeoOfIso hU.isoSpec).toEquiv
  let E := E₁.trans E₂
  let _ : Fintype Subtype (fun x : Spec (CommRingCat.of k) ⟶ X => x ≫ f = 𝟙 (Spec (CommRingCat.of k))) := Fintype.ofEquiv _ E.symm
  rw [finsum_eq_sum_of_fintype, ← Equiv.sum_comp E]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hEy : y.1.base (IsLocalRing.closedPoint k) = (E₁ y).1 := rfl
  have hpy : E y = hU.primeIdealOf (E₁ y) := rfl
  let _ := hU.isLocalization_stalk (E₁ y)
  rw [hEy, hpy]
  apply length_self_eq_of_ringEquiv (IsLocalization.algEquiv (hU.primeIdealOf (E₁ y)).asIdeal.primeCompl
    (Localization.AtPrime (hU.primeIdealOf (E₁ y)).asIdeal) (X.presheaf.stalk (E₁ y).1)).toRingEquiv


-- created on 2026-10-20

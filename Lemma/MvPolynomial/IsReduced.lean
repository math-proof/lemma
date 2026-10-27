import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000


private abbrev MinP (A : Type*) [CommRing A] := ↥(minimalPrimes A)

private lemma isPrime_of_mem_minimalPrimes
  {A : Type u} [CommRing A]
  {p : Ideal A}
-- given
  (hp : p ∈ minimalPrimes A) :
-- imply
  p.IsPrime := by
-- proof
  apply hp.1.1

private lemma sInf_minimalPrimes_eq_bot
  [CommRing A] [IsReduced A] :
-- imply
  sInf (minimalPrimes A) = (⊥ : Ideal A) := by
-- proof
  have h : sInf ((⊥ : Ideal A).minimalPrimes) = (⊥ : Ideal A).radical := Ideal.sInf_minimalPrimes
  rw [minimalPrimes, h]
  apply nilradical_eq_zero

noncomputable instance {A : Type*} [CommRing A] [IsNoetherianRing A] : Fintype (MinP A) := by
  apply (minimalPrimes.finite_of_isNoetherianRing (R := A)).fintype

instance {A : Type*} [CommRing A] (p : MinP A) : p.1.IsPrime := by
  apply isPrime_of_mem_minimalPrimes p.2

instance {A : Type*} [CommRing A] (p : MinP A) : IsDomain (A ⧸ p.1) := by
  apply Ideal.Quotient.isDomain p.1

private noncomputable def toProd
  {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] [IsNoetherianRing A] :
    A →ₐ[k] (∀ p : MinP A, FractionRing (A ⧸ p.1)) :=
  AlgHom.pi fun p =>
    (IsScalarTower.toAlgHom k (A ⧸ p.1) (FractionRing (A ⧸ p.1))).comp
      (Ideal.Quotient.mkₐ k p.1)

private lemma toProd_apply
  {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] [IsNoetherianRing A]
  (a : A) (p : MinP A) :
    toProd (k := k) a p =
      algebraMap (A ⧸ p.1) (FractionRing (A ⧸ p.1)) (Ideal.Quotient.mk p.1 a) := by
  rfl

private lemma toProd_injective
  {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] [IsNoetherianRing A] [IsReduced A] :
    Function.Injective (toProd (k := k) (A := A)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hmem : ∀ p : MinP A, a ∈ p.1 := by
    intro p
    have := congrFun ha p
    rwa [toProd_apply, Pi.zero_apply,
      map_eq_zero_iff _ (IsFractionRing.injective (A ⧸ p.1) (FractionRing (A ⧸ p.1))),
      Ideal.Quotient.eq_zero_iff_mem] at this
  have : a ∈ sInf (minimalPrimes A) := by
    rw [Submodule.mem_sInf]
    exact fun p hp => hmem ⟨p, hp⟩
  rwa [sInf_minimalPrimes_eq_bot, Submodule.mem_bot] at this

private lemma isReduced_tensor_of_forall_minimalPrimes
  [Field k] [CommRing A] [Algebra k A]
  [IsNoetherianRing A] [IsReduced A]
  [Field K] [Algebra k K]
-- given
  (h : ∀ p ∈ minimalPrimes A, IsReduced (K ⊗[k] FractionRing (A ⧸ p))) :
-- imply
  IsReduced (K ⊗[k] A) := by
-- proof
  classical
  let B : MinP A → Type _ := fun p => FractionRing (A ⧸ p.1)
  let e : K ⊗[k] (∀ p : MinP A, B p) ≃ₐ[K] (∀ p : MinP A, K ⊗[k] B p) :=
    Algebra.TensorProduct.piRight k K K B
  let m : K ⊗[k] A →ₐ[K] K ⊗[k] (∀ p : MinP A, B p) :=
    Algebra.TensorProduct.map (AlgHom.id K K) (toProd (k := k))
  have hm : Function.Injective m := by
    have h1 : Function.Injective ((toProd (k := k) (A := A)).toLinearMap.lTensor K) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (toProd_injective (k := k))
    intro x y hxy
    exact h1 hxy
  have : ∀ p : MinP A, IsReduced (K ⊗[k] B p) := fun p => h p.1 p.2
  apply isReduced_of_injective (e.toAlgHom.comp m) (e.injective.comp hm)

private noncomputable def polyToE
  {k K : Type*} [Field k] [Field K] [Algebra k K] (ι : Type*) :
    MvPolynomial ι k →+* FractionRing (MvPolynomial ι K) :=
  (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K))).comp
    (MvPolynomial.map (algebraMap k K))

private lemma polyToE_injective
  {k K : Type*} [Field k] [Field K] [Algebra k K] (ι : Type*) :
    Function.Injective (polyToE (k := k) (K := K) ι) := by
  apply (IsFractionRing.injective (MvPolynomial ι K) (FractionRing (MvPolynomial ι K))).comp
    (MvPolynomial.map_injective _ (algebraMap k K).injective)

private lemma fracToE_commutes
  {k K : Type*} [Field k] [Field K] [Algebra k K] (ι : Type*) (c : k) :
    IsFractionRing.lift (polyToE_injective (k := k) (K := K) ι)
      (algebraMap k (FractionRing (MvPolynomial ι k)) c) =
      algebraMap k (FractionRing (MvPolynomial ι K)) c := by
  rw [IsScalarTower.algebraMap_apply k (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)),
    IsFractionRing.lift_algebraMap, polyToE, RingHom.comp_apply, MvPolynomial.algebraMap_eq,
    MvPolynomial.map_C,
    IsScalarTower.algebraMap_apply k K (FractionRing (MvPolynomial ι K)),
    IsScalarTower.algebraMap_apply K (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)),
    MvPolynomial.algebraMap_eq]

private noncomputable def fracToE
  {k K : Type*} [Field k] [Field K] [Algebra k K] (ι : Type*) :
    FractionRing (MvPolynomial ι k) →ₐ[k] FractionRing (MvPolynomial ι K) :=
  AlgHom.mk (IsFractionRing.lift (polyToE_injective (k := k) (K := K) ι)) (fracToE_commutes (k := k) (K := K) ι)

private lemma fracToE_algebraMap
  {k K : Type*} [Field k] [Field K] [Algebra k K] (ι : Type*) (p : MvPolynomial ι k) :
    fracToE (k := k) (K := K) ι (algebraMap (MvPolynomial ι k) _ p) =
      polyToE (k := k) (K := K) ι p := by
  show IsFractionRing.lift (polyToE_injective (k := k) (K := K) ι) _ = _
  apply IsFractionRing.lift_algebraMap

private noncomputable def liftFrac
  {k K : Type*} [Field k] [Field K] [Algebra k K] (ι : Type*) :
    K ⊗[k] FractionRing (MvPolynomial ι k) →ₐ[k] FractionRing (MvPolynomial ι K) :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom k K _) (fracToE (k := k) (K := K) ι)
    (fun _ _ => Commute.all _ _)

private noncomputable def inclPoly
  {k K : Type*} [Field k] [Field K] [Algebra k K] (ι : Type*) :
    K ⊗[k] MvPolynomial ι k →ₐ[k] K ⊗[k] FractionRing (MvPolynomial ι k) :=
  Algebra.TensorProduct.map (AlgHom.id k K)
    (IsScalarTower.toAlgHom k (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)))

private lemma liftFrac_comp_inclPoly_apply
  {k K : Type*} [Field k] [Field K] [Algebra k K] (ι : Type*)
  (w : K ⊗[k] MvPolynomial ι k) :
    liftFrac (k := k) (K := K) ι (inclPoly (k := k) (K := K) ι w) =
      algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K))
        (MvPolynomial.algebraTensorAlgEquiv k K w) := by
  refine TensorProduct.inductionOn w ?_ ?_
  ·
    intro a p
    simp only [inclPoly, liftFrac, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
      IsScalarTower.coe_toAlgHom', Algebra.TensorProduct.lift_tmul, fracToE_algebraMap,
      MvPolynomial.algebraTensorAlgEquiv_tmul, Algebra.smul_def, map_mul, polyToE,
      RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial ι K) (FractionRing (MvPolynomial ι K))]
  ·
    intro x y hx hy
    simp only [map_add, hx, hy]

private lemma liftFrac_inclPoly_injective
  {k K : Type*} [Field k] [Field K] [Algebra k K] (ι : Type*) :
    Function.Injective (fun w => liftFrac (k := k) (K := K) ι (inclPoly (k := k) (K := K) ι w)) := by
  intro w₁ w₂ h
  simp only [liftFrac_comp_inclPoly_apply] at h
  apply (MvPolynomial.algebraTensorAlgEquiv k K).injective
  apply IsFractionRing.injective (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) h

private lemma exists_denom
  {k K : Type*} [Field k] [Field K] [Algebra k K] (ι : Type*)
  (z : K ⊗[k] FractionRing (MvPolynomial ι k)) :
    ∃ s : MvPolynomial ι k, s ≠ 0 ∧ ∃ w : K ⊗[k] MvPolynomial ι k,
      ((1 : K) ⊗ₜ[k] algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) s) * z =
        inclPoly (k := k) (K := K) ι w := by
  refine TensorProduct.inductionOn z ?_ ?_
  ·
    intro a f
    obtain ⟨⟨p, s⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (nonZeroDivisors (MvPolynomial ι k)) f
    refine ⟨s.1, nonZeroDivisors.ne_zero s.2, a ⊗ₜ p, ?_⟩
    simp only [inclPoly, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
      IsScalarTower.coe_toAlgHom', Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [mul_comm, IsLocalization.mk'_spec]
  ·
    intro x y hx hy
    obtain ⟨s₁, hs₁, w₁, h₁⟩ := hx
    obtain ⟨s₂, hs₂, w₂, h₂⟩ := hy
    refine ⟨s₁ * s₂, mul_ne_zero hs₁ hs₂, ((1 : K) ⊗ₜ s₂) * w₁ + ((1 : K) ⊗ₜ s₁) * w₂, ?_⟩
    have e : ((1 : K) ⊗ₜ[k] algebraMap (MvPolynomial ι k)
        (FractionRing (MvPolynomial ι k)) (s₁ * s₂)) =
        ((1 : K) ⊗ₜ[k] algebraMap _ (FractionRing (MvPolynomial ι k)) s₁) *
          ((1 : K) ⊗ₜ[k] algebraMap _ (FractionRing (MvPolynomial ι k)) s₂) := by
      rw [map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have i₁ : inclPoly (k := k) (K := K) ι ((1 : K) ⊗ₜ s₁) =
        (1 : K) ⊗ₜ algebraMap _ (FractionRing (MvPolynomial ι k)) s₁ := by
      simp [inclPoly]
    have i₂ : inclPoly (k := k) (K := K) ι ((1 : K) ⊗ₜ s₂) =
        (1 : K) ⊗ₜ algebraMap _ (FractionRing (MvPolynomial ι k)) s₂ := by
      simp [inclPoly]
    rw [e, mul_add, map_add, map_mul, map_mul, i₁, i₂, ← h₁, ← h₂]
    ring

private lemma liftFrac_injective
  {k K : Type*} [Field k] [Field K] [Algebra k K] (ι : Type*) :
    Function.Injective (liftFrac (k := k) (K := K) ι) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨s, hs, w, hw⟩ := exists_denom (k := k) (K := K) ι z
  have h1 : liftFrac (k := k) (K := K) ι (inclPoly (k := k) (K := K) ι w) = 0 := by
    rw [← hw, map_mul, hz, mul_zero]
  have hw0 : w = 0 :=
    liftFrac_inclPoly_injective (k := k) (K := K) ι (by simpa using h1)
  rw [hw0, map_zero] at hw
  have hsF : algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) s ≠ 0 :=
    fun h => hs ((IsFractionRing.injective _ _) (by rw [h, map_zero]))
  have hunit : ((1 : K) ⊗ₜ[k] (algebraMap (MvPolynomial ι k)
      (FractionRing (MvPolynomial ι k)) s)⁻¹) *
      ((1 : K) ⊗ₜ[k] algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) s) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hsF]
    rfl
  calc
    _ = (((1 : K) ⊗ₜ[k] (algebraMap (MvPolynomial ι k)
        (FractionRing (MvPolynomial ι k)) s)⁻¹) *
        ((1 : K) ⊗ₜ[k] algebraMap (MvPolynomial ι k)
          (FractionRing (MvPolynomial ι k)) s)) * z := by rw [hunit, one_mul]
    _ = 0 := by rw [mul_assoc, hw, mul_zero]

private noncomputable def toEAlgHom
  {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K]
  {L : Type*} [Field L] [Algebra k L] {ι : Type*}
  (x : ι → L) (hx : AlgebraicIndependent k x) :
    ↥(IntermediateField.adjoin k (Set.range x)) →ₐ[k] FractionRing (MvPolynomial ι K) :=
  (fracToE (k := k) (K := K) ι).comp (hx.aevalEquivField.symm :
    ↥(IntermediateField.adjoin k (Set.range x)) →ₐ[k] _)

private lemma injective_liftToE
  {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K]
  {L : Type*} [Field L] [Algebra k L] {ι : Type*}
  (x : ι → L) (hx : AlgebraicIndependent k x) :
    Function.Injective (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom k K (FractionRing (MvPolynomial ι K)))
      (toEAlgHom (K := K) x hx) (fun _ _ => Commute.all _ _)) := by
  let e : K ⊗[k] ↥(IntermediateField.adjoin k (Set.range x)) ≃ₐ[k]
    K ⊗[k] FractionRing (MvPolynomial ι k) :=
    Algebra.TensorProduct.congr AlgEquiv.refl hx.aevalEquivField.symm
  have hfac : (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom k K (FractionRing (MvPolynomial ι K)))
      (toEAlgHom (K := K) x hx) (fun _ _ => Commute.all _ _)) =
      (liftFrac (k := k) (K := K) ι).comp e.toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro a f
    simp [liftFrac, toEAlgHom, e]
  rw [hfac]
  apply (liftFrac_injective (k := k) (K := K) ι).comp e.injective

private lemma isReduced_tensor_of_isSeparable
  (F E L : Type*) [Field F] [Field E] [Field L] [Algebra F E] [Algebra F L]
  [Algebra.IsSeparable F L] [Algebra.EssFiniteType F L] :
    IsReduced (L ⊗[F] E) := by
  have : Algebra.FormallyEtale F L := Algebra.FormallyEtale.of_isSeparable F L
  have : Algebra.FormallyUnramified E (E ⊗[F] L) := inferInstance
  have : Algebra.EssFiniteType E (E ⊗[F] L) := inferInstance
  have : IsReduced (E ⊗[F] L) := Algebra.FormallyUnramified.isReduced_of_field E (E ⊗[F] L)
  apply isReduced_of_injective (Algebra.TensorProduct.comm F L E)
    (Algebra.TensorProduct.comm F L E).injective

private lemma isReduced_tensor_of_injective
  [Field k] [Field F] [Field K] [Field E] [Field L]
  [Algebra k F] [Algebra k K] [Algebra k E] [Algebra F E] [Algebra K E]
  [IsScalarTower k F E] [IsScalarTower k K E]
  [Algebra k L] [Algebra F L] [IsScalarTower k F L]
  [Algebra.IsSeparable F L] [Algebra.EssFiniteType F L]
-- given
  (hψ : Function.Injective (Algebra.TensorProduct.lift (Algebra.ofId F E)
    (IsScalarTower.toAlgHom k K E) (fun _ _ => Commute.all _ _) : F ⊗[k] K →ₐ[F] E)) :
-- imply
  IsReduced (K ⊗[k] L) := by
-- proof
  have : IsReduced (L ⊗[F] E) := isReduced_tensor_of_isSeparable F E L
  set ψ : F ⊗[k] K →ₐ[F] E := Algebra.TensorProduct.lift (Algebra.ofId F E)
    (IsScalarTower.toAlgHom k K E) (fun _ _ => Commute.all _ _)
  let φ : L ⊗[F] (F ⊗[k] K) →ₐ[F] L ⊗[F] E := Algebra.TensorProduct.map (AlgHom.id F L) ψ
  have hφ : Function.Injective φ :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := L) ψ.toLinearMap hψ
  let e : K ⊗[k] L ≃ₐ[k] L ⊗[F] (F ⊗[k] K) :=
    (Algebra.TensorProduct.comm k K L).trans
      ((Algebra.TensorProduct.cancelBaseChange k F F L K).symm.restrictScalars k)
  apply isReduced_of_injective ((φ.restrictScalars k).comp e.toAlgHom) (hφ.comp e.injective)

private lemma isReduced_tensor_of_adjoin_of_isSeparable
  [Field k] [Field K] [Algebra k K]
  [Field L] [Algebra k L]
  {x : ι → L} [Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) L] [Algebra.EssFiniteType (IntermediateField.adjoin k (Set.range x)) L]
-- given
  (hx : AlgebraicIndependent k x) :
-- imply
  IsReduced (K ⊗[k] L) := by
-- proof
  let _ : Algebra (IntermediateField.adjoin k (Set.range x)) (FractionRing (MvPolynomial ι K)) :=
    (toEAlgHom (K := K) x hx).toRingHom.toAlgebra
  have : IsScalarTower k (IntermediateField.adjoin k (Set.range x))
    (FractionRing (MvPolynomial ι K)) :=
    IsScalarTower.of_algebraMap_eq (fun c => ((toEAlgHom (K := K) x hx).commutes c).symm)
  refine isReduced_tensor_of_injective
    (F := IntermediateField.adjoin k (Set.range x))
    (E := FractionRing (MvPolynomial ι K)) ?_
  have h1 := injective_liftToE (K := K) x hx
  set ψ := (Algebra.TensorProduct.lift
    (Algebra.ofId (IntermediateField.adjoin k (Set.range x)) (FractionRing (MvPolynomial ι K)))
    (IsScalarTower.toAlgHom k K (FractionRing (MvPolynomial ι K)))
    (fun _ _ => Commute.all _ _) :
    (IntermediateField.adjoin k (Set.range x)) ⊗[k] K →ₐ[IntermediateField.adjoin k (Set.range x)]
      FractionRing (MvPolynomial ι K))
  have heq : ∀ z, ψ z = (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom k K (FractionRing (MvPolynomial ι K)))
      (toEAlgHom (K := K) x hx) (fun _ _ => Commute.all _ _))
      (Algebra.TensorProduct.comm k _ K z) := by
    intro z
    refine TensorProduct.inductionOn z ?_ ?_
    ·
      intro a b
      simp only [ψ, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.comm_tmul]
      rw [mul_comm]
      rfl
    ·
      intro a b ha hb
      simp only [map_add, ha, hb]
  intro z w hzw
  have : Algebra.TensorProduct.comm k _ K z = Algebra.TensorProduct.comm k _ K w :=
    h1 (by rw [← heq, ← heq, hzw])
  apply (Algebra.TensorProduct.comm k _ K).injective this

private lemma isReduced_tensor_field_of_perfectField
  {k : Type*} [Field k] [PerfectField k]
  {L : Type*} [Field L] [Algebra k L] [Algebra.EssFiniteType k L]
  {K : Type*} [Field K] [Algebra k K] :
    IsReduced (K ⊗[k] L) := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k L
  have hrange : Set.range ((↑) : s → L) = (s : Set L) := Subtype.range_coe
  have : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : s → L))) L := by
    rwa [hrange]
  have : Algebra.EssFiniteType (IntermediateField.adjoin k (Set.range ((↑) : s → L))) L :=
    Algebra.EssFiniteType.of_comp k _ L
  apply isReduced_tensor_of_adjoin_of_isSeparable (K := K) (x := ((↑) : s → L)) hs.1


/--
[Algebra_TensorProduct_isReduced_of_perfectField_of_isReduced](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_TensorProduct_isReduced_of_perfectField_of_isReduced.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k] [PerfectField k]
  {A : Type v} [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A]
  {K : Type w} [Field K] [Algebra k K] :
-- imply
  IsReduced (K ⊗[k] A) := by
-- proof
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  refine isReduced_tensor_of_forall_minimalPrimes (K := K) (fun p hp => ?_)
  have : p.IsPrime := hp.1.1
  have : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
  have : Algebra.FiniteType k (A ⧸ p) :=
    Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have : Algebra.EssFiniteType k (FractionRing (A ⧸ p)) :=
    Algebra.EssFiniteType.comp k (A ⧸ p) (FractionRing (A ⧸ p))
  apply isReduced_tensor_field_of_perfectField
    (L := FractionRing (A ⧸ p)) (K := K)


-- created on 2026-10-13

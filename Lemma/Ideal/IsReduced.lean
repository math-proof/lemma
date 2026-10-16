import Mathlib
import sympy.Basic
open scoped TensorProduct IntermediateField.algebraAdjoinAdjoin


private lemma isDomain_tensorProduct_of_isFractionRing
  [Field k] [CommRing P] [Algebra k P] [Field E] [Algebra k E]
  [Algebra P E] [IsScalarTower k P E] [IsFractionRing P E] [Field L] [Algebra k L]
-- given
  [IsDomain (P ⊗[k] L)] :
-- imply
  IsDomain (E ⊗[k] L) := by
-- proof
  let f : P ⊗[k] L →ₐ[k] E ⊗[k] L :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k P E) (AlgHom.id k L)
  let _ : Algebra (P ⊗[k] L) (E ⊗[k] L) := f.toRingHom.toAlgebra
  have hf : ∀ x : P ⊗[k] L, algebraMap (P ⊗[k] L) (E ⊗[k] L) x = f x := fun _ => rfl
  have : IsScalarTower P (P ⊗[k] L) (E ⊗[k] L) := by
    refine IsScalarTower.of_algebraMap_eq (R := P) (S := P ⊗[k] L) (A := E ⊗[k] L) fun x => ?_
    rw [hf, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
    simp [f]
  have H : (algebraMap (P ⊗[k] L) (E ⊗[k] L)).comp
    Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom := by
    ext x
    simp [hf, f]
  have : IsLocalization (Algebra.algebraMapSubmonoid (P ⊗[k] L) (nonZeroDivisors P))
    (E ⊗[k] L) :=
    IsLocalization.tensorProduct_tensorProduct k L (nonZeroDivisors P) E H
  have hinj : Function.Injective
    (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] L) :=
    Algebra.TensorProduct.includeLeft_injective (S := k) (algebraMap k L).injective
  have : IsDomain P := hinj.isDomain _
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (E ⊗[k] L)
    (M := Algebra.algebraMapSubmonoid (P ⊗[k] L) (nonZeroDivisors P)) ?_
  intro _ h
  obtain ⟨x, hx, rfl⟩ := h
  refine mem_nonZeroDivisors_of_ne_zero ?_
  have hx0 : x ≠ 0 := nonZeroDivisors.ne_zero hx
  intro h
  apply hx0
  apply hinj
  rw [map_zero]
  simpa [Algebra.TensorProduct.algebraMap_apply] using h

private lemma isDomain_adjoin_tensorProduct
  [Field k] [Field K] [Algebra k K] [Field L] [Algebra k L]
  {v : ι → K}
-- given
  (hv : AlgebraicIndependent k v) :
-- imply
  IsDomain ((IntermediateField.adjoin k (Set.range v)) ⊗[k] L) := by
-- proof
  classical
  have : IsDomain ((Algebra.adjoin k (Set.range v)) ⊗[k] L) := by
    let e : (Algebra.adjoin k (Set.range v)) ⊗[k] L ≃ₐ[k] MvPolynomial ι L :=
      (Algebra.TensorProduct.congr hv.aevalEquiv.symm AlgEquiv.refl).trans
        ((Algebra.TensorProduct.comm k _ _).trans
          ((MvPolynomial.scalarRTensorAlgEquiv (R := k) (σ := ι) (N := L)).restrictScalars k))
    apply e.toMulEquiv.isDomain (MvPolynomial ι L)
  apply isDomain_tensorProduct_of_isFractionRing (k := k) (P := Algebra.adjoin k (Set.range v))

private lemma isReduced_tensorProduct_of_formallyUnramified_of_isDomain
  (E K D : Type*) [Field E] [Field K] [Algebra E K] [Algebra.FormallyUnramified E K]
  [Algebra.EssFiniteType E K] [CommRing D] [Algebra E D] [IsDomain D] :
-- imply
  IsReduced (K ⊗[E] D) := by
-- proof
  let F := FractionRing D
  have : IsReduced (F ⊗[E] K) := Algebra.FormallyUnramified.isReduced_of_field F (F ⊗[E] K)
  have : IsReduced (K ⊗[E] F) :=
    isReduced_of_injective (Algebra.TensorProduct.comm E K F)
      (Algebra.TensorProduct.comm E K F).injective
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id E K) (IsScalarTower.toAlgHom E D F)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := K)
      (IsScalarTower.toAlgHom E D F).toLinearMap (IsFractionRing.injective D F)
  refine isReduced_of_injective _ hinj

private lemma isReduced_tensorProduct_of_isSeparable_of_isDomain
  (k E K L : Type*) [Field k] [Field E] [Field K] [Field L] [Algebra k E] [Algebra k K]
  [Algebra E K] [IsScalarTower k E K] [Algebra k L] [Algebra.IsSeparable E K]
  [Algebra.EssFiniteType E K] [IsDomain (E ⊗[k] L)] :
-- imply
  IsReduced (L ⊗[k] K) := by
-- proof
  have : Algebra.FormallyUnramified E K := Algebra.FormallyUnramified.of_isSeparable E K
  have : IsReduced (K ⊗[E] (E ⊗[k] L)) :=
    isReduced_tensorProduct_of_formallyUnramified_of_isDomain E K (E ⊗[k] L)
  let e₁ : K ⊗[E] (E ⊗[k] L) ≃ₐ[E] K ⊗[k] L :=
    Algebra.TensorProduct.cancelBaseChange k E E K L
  let e₂ : K ⊗[k] L ≃ₐ[k] L ⊗[k] K := Algebra.TensorProduct.comm k K L
  have : IsReduced (K ⊗[k] L) := isReduced_of_injective e₁.symm e₁.symm.injective
  apply isReduced_of_injective e₂.symm e₂.symm.injective

private lemma isReduced_tensorProduct_field_of_essFiniteType
  (k K L : Type*) [Field k] [PerfectField k] [Field K] [Algebra k K]
  [Algebra.EssFiniteType k K] [Field L] [Algebra k L] :
-- imply
  IsReduced (L ⊗[k] K) := by
-- proof
  classical
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  have hrange : Set.range ((↑) : s → K) = (s : Set K) := by simp
  have : IsDomain ((IntermediateField.adjoin k (s : Set K)) ⊗[k] L) := by
    have := isDomain_adjoin_tensorProduct (L := L) hs.1
    rwa [hrange] at this
  have : Algebra.EssFiniteType (IntermediateField.adjoin k (s : Set K)) K :=
    Algebra.EssFiniteType.of_comp k _ K
  apply isReduced_tensorProduct_of_isSeparable_of_isDomain k
    (IntermediateField.adjoin k (s : Set K)) K L

private lemma isReduced_tensorProduct_of_finiteType
  (k B L : Type*) [Field k] [PerfectField k] [CommRing B] [Algebra k B] [IsReduced B]
  [Algebra.FiniteType k B] [Field L] [Algebra k L] :
-- imply
  IsReduced (L ⊗[k] B) := by
-- proof
  classical
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hfin : (minimalPrimes B).Finite := minimalPrimes.finite_of_isNoetherianRing B
  have : Fintype (minimalPrimes B) := hfin.fintype
  have hprime : ∀ p : minimalPrimes B, (p.1).IsPrime := fun p => p.2.1.1
  let K : minimalPrimes B → Type _ := fun p => FractionRing (B ⧸ p.1)
  let φ : B →ₐ[k] (∀ p, K p) :=
    AlgHom.pi fun p =>
      (IsScalarTower.toAlgHom k (B ⧸ p.1) (K p)).comp (Ideal.Quotient.mkₐ k p.1)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have hb' : ∀ p : minimalPrimes B, b ∈ p.1 := by
      intro p
      have h2 : algebraMap (B ⧸ p.1) (K p) (Ideal.Quotient.mk p.1 b) = 0 := congr_fun hb p
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      apply (IsFractionRing.injective (B ⧸ p.1) (K p))
      rw [h2, map_zero]
    have hmem : b ∈ sInf (minimalPrimes B) := by
      rw [Submodule.mem_sInf]
      exact fun p hp => hb' ⟨p, hp⟩
    have hsInf : sInf (minimalPrimes B) = (⊥ : Ideal B) := by
      change sInf ((⊥ : Ideal B).minimalPrimes) = ⊥
      rw [Ideal.sInf_minimalPrimes]
      exact nilradical_eq_zero B
    rw [hsInf] at hmem
    exact (Submodule.mem_bot B).mp hmem
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id L L) φ) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := L) φ.toLinearMap hφ
  have : ∀ p, IsReduced (L ⊗[k] K p) := fun p =>
    isReduced_tensorProduct_field_of_essFiniteType k (K p) L
  have : IsReduced (L ⊗[k] (∀ p, K p)) :=
    isReduced_of_injective (Algebra.TensorProduct.piRight k k L K)
      (Algebra.TensorProduct.piRight k k L K).injective
  apply isReduced_of_injective _ hinj


/--
[Algebra_isReduced_tensorProduct_of_perfectField](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_isReduced_tensorProduct_of_perfectField.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k] [PerfectField k]
  {A : Type v} [CommRing A] [Algebra k A] [IsReduced A]
  {L : Type w} [Field L] [Algebra k L] :
-- imply
  IsReduced (L ⊗[k] A) := by
-- proof
  refine IsReduced.tensorProduct_of_flat_of_forall_fg fun B hB => ?_
  have : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
  have : Algebra.FiniteType k B := ⟨(Subalgebra.fg_top B).mpr hB⟩
  apply isReduced_tensorProduct_of_finiteType k B L


-- created on 2026-10-13

import Mathlib
import sympy.Basic
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct nonZeroDivisors


private lemma trace_one_tmul
  [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B] [Module.Free R B] [Module.Finite R B]
  {x : B} :
-- imply
  Algebra.trace A (A ⊗[R] B) ((1 : A) ⊗ₜ[R] x) = algebraMap R A (Algebra.trace R B x) := by
-- proof
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange ((Algebra.lmul R B) x) A]
  congr 1
  refine LinearMap.ext fun z => ?_
  refine TensorProduct.inductionOn (motive := fun z =>
      ((Algebra.lmul A (A ⊗[R] B)) ((1 : A) ⊗ₜ[R] x)) z =
        (LinearMap.baseChange A ((Algebra.lmul R B) x)) z) z ?_ ?_
  ·
    intro a b
    simp only [LinearMap.baseChange_tmul, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  ·
    intro x y hx hy
    simp only [map_add, hx, hy]


/--
[Algebra_TensorProduct_isDomain_and_isIntegrallyClosed_of_isField_of_isSeparable](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_TensorProduct_isDomain_and_isIntegrallyClosed_of_isField_of_isSeparable.lean)
-/
@[path]
private lemma main
  {k₀ S F L : Type u} [Field k₀] [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra k₀ S] [Field F] [Algebra k₀ F] [Algebra S F] [IsScalarTower k₀ S F] [IsFractionRing S F] [Field L] [Algebra k₀ L] [FiniteDimensional k₀ L] [Algebra.IsSeparable k₀ L]
-- given
  (hF : IsField (F ⊗[k₀] L)) :
-- imply
  IsDomain (L ⊗[k₀] S) ∧ IsIntegrallyClosed (L ⊗[k₀] S) := by
-- proof
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable k₀ L
  have hd0 : Algebra.discr k₀ ⇑pb.basis ≠ 0 := Algebra.discr_not_zero_of_basis k₀ pb.basis
  have hint : IsIntegral S ((1 : F) ⊗ₜ[k₀] pb.gen) := by
    apply ((Algebra.IsIntegral.isIntegral (R := k₀) pb.gen).map (Algebra.TensorProduct.includeRight : L →ₐ[k₀] F ⊗[k₀] L)).tower_top
  have hclos : ∀ z : F ⊗[k₀] L, IsIntegral S z →
      z ∈ Algebra.adjoin S {(1 : F) ⊗ₜ[k₀] pb.gen} := by
    let _ : Field (F ⊗[k₀] L) := hF.toField
    let _ : Algebra.FormallyUnramified k₀ L := Algebra.FormallyUnramified.of_isSeparable k₀ L
    let _ : Algebra.IsSeparable F (F ⊗[k₀] L) :=
      Algebra.FormallyUnramified.isSeparable F (F ⊗[k₀] L)
    let bE := Algebra.TensorProduct.basis F pb.basis
    have hb : ∀ i, bE i = (1 : F) ⊗ₜ[k₀] pb.basis i := fun i => Algebra.TensorProduct.basis_apply _ _
    let pbE : PowerBasis F (F ⊗[k₀] L) :=
      { gen := (1 : F) ⊗ₜ pb.gen, dim := pb.dim, basis := bE,
        basis_eq_pow := fun i => by
          rw [hb, pb.basis_eq_pow, Algebra.TensorProduct.tmul_pow, one_pow] }
    have hgen : pbE.gen = (1 : F) ⊗ₜ[k₀] pb.gen := rfl
    have hint' : IsIntegral S pbE.gen := hint
    have key : ∀ z : F ⊗[k₀] L, IsIntegral S z →
        Algebra.discr F (⇑pbE.basis) • z ∈ Algebra.adjoin S {pbE.gen} :=
      fun z hz => Algebra.discr_mul_isIntegral_mem_adjoin F hint' hz
    have hdisc : Algebra.discr F (⇑pbE.basis) = algebraMap k₀ F (Algebra.discr k₀ ⇑pb.basis) := by
      rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
      congr 1
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
        Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.traceForm_apply]
      have hbb : pbE.basis i * pbE.basis j = (1 : F) ⊗ₜ[k₀] (pb.basis i * pb.basis j) := by
        show bE i * bE j = _
        rw [hb, hb, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [hbb]
      apply trace_one_tmul
    intro z hz
    have h1 := key z hz
    rw [hdisc, Algebra.smul_def, hgen] at h1
    have h2 : algebraMap F (F ⊗[k₀] L) (algebraMap k₀ F (Algebra.discr k₀ ⇑pb.basis)) =
        algebraMap S (F ⊗[k₀] L) (algebraMap k₀ S (Algebra.discr k₀ ⇑pb.basis)) := by
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    have h3 : z = algebraMap S (F ⊗[k₀] L) (algebraMap k₀ S (Algebra.discr k₀ ⇑pb.basis)⁻¹) *
        (algebraMap F (F ⊗[k₀] L) (algebraMap k₀ F (Algebra.discr k₀ ⇑pb.basis)) * z) := by
      rw [h2, ← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel₀ hd0, map_one, map_one, one_mul]
    rw [h3]
    apply Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) h1
  let _ : IsDomain (F ⊗[k₀] L) := by
    let _ : Field (F ⊗[k₀] L) := hF.toField
    infer_instance
  set C : Subalgebra S (F ⊗[k₀] L) := Algebra.adjoin S {(1 : F) ⊗ₜ[k₀] pb.gen} with hCdef
  have hCfg : (Subalgebra.toSubmodule C).FG :=
    fg_adjoin_of_finite (Set.finite_singleton _) (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      apply hint)
  let _ : Algebra.IsIntegral S C := ⟨fun c =>
    (isIntegral_algHom_iff C.val Subtype.val_injective).mp (IsIntegral.of_mem_of_fg C hCfg _ c.2)⟩
  have hIC : IsIntegrallyClosed C := by
    rw [isIntegrallyClosed_iff (FractionRing C)]
    intro x hx
    have hunit : ∀ y : nonZeroDivisors C, IsUnit (algebraMap C (F ⊗[k₀] L) y) := by
      intro y
      have hy0 : (algebraMap C (F ⊗[k₀] L) y) ≠ 0 := by
        intro h
        apply nonZeroDivisors.ne_zero y.2 (Subtype.ext h)
      obtain ⟨b, hb⟩ := hF.mul_inv_cancel hy0
      apply IsUnit.of_mul_eq_one b hb
    let φ : FractionRing C →ₐ[C] F ⊗[k₀] L :=
      { toRingHom := IsLocalization.lift (M := nonZeroDivisors C) hunit
        commutes' := fun a => by
          apply IsLocalization.lift_eq hunit a }
    have hφ : ∀ a : C, φ (algebraMap C (FractionRing C) a) = (a : F ⊗[k₀] L) :=
      fun a => IsLocalization.lift_eq hunit a
    have hx' : IsIntegral C (φ x) := hx.map φ
    have hxS : IsIntegral S (φ x) := isIntegral_trans _ hx'
    have hmem : φ x ∈ C := hclos _ hxS
    refine ⟨⟨φ x, hmem⟩, ?_⟩
    apply (φ : FractionRing C →+* F ⊗[k₀] L).injective
    apply hφ
  let f₀ : S →ₐ[k₀] F := IsScalarTower.toAlgHom k₀ S F
  let ψ₀ : S ⊗[k₀] L →ₐ[k₀] F ⊗[k₀] L := Algebra.TensorProduct.map f₀ (AlgHom.id k₀ L)
  have hinjSF : Function.Injective (algebraMap S F) := IsFractionRing.injective S F
  have hψ₀ : Function.Injective ψ₀ := by
    have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := L) f₀.toLinearMap hinjSF
    have h2 : ∀ x, ψ₀ x = LinearMap.rTensor L f₀.toLinearMap x := by
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul a b => simp [ψ₀]
      | add x y hx hy => simp [map_add, hx, hy]
    intro x y hxy
    apply h1
    rw [← h2 x, ← h2 y, hxy]
  let ψ : L ⊗[k₀] S →ₐ[k₀] F ⊗[k₀] L :=
    ψ₀.comp (Algebra.TensorProduct.comm k₀ L S : L ⊗[k₀] S →ₐ[k₀] S ⊗[k₀] L)
  have hψ : Function.Injective ψ := hψ₀.comp (Algebra.TensorProduct.comm k₀ L S).injective
  have hψt : ∀ (l : L) (s : S), ψ (l ⊗ₜ s) = algebraMap S F s ⊗ₜ l := by
    intro l s
    simp [ψ, ψ₀, f₀]
  have hψt' : ∀ (l : L) (s : S), ψ (l ⊗ₜ s) =
      algebraMap S (F ⊗[k₀] L) s * ((1 : F) ⊗ₜ[k₀] l) := by
    intro l s
    rw [hψt, IsScalarTower.algebraMap_apply S F (F ⊗[k₀] L), Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have h1L : ∀ l : L, (1 : F) ⊗ₜ[k₀] l ∈ C := by
    intro l
    obtain ⟨q, hq⟩ := pb.exists_eq_aeval' l
    have : (1 : F) ⊗ₜ[k₀] l = Polynomial.aeval ((1 : F) ⊗ₜ[k₀] pb.gen) q := by
      rw [hq]
      apply Eq.symm
      apply Polynomial.aeval_algHom_apply
        (Algebra.TensorProduct.includeRight : L →ₐ[k₀] F ⊗[k₀] L) pb.gen q
    rw [this]
    have hθC : (1 : F) ⊗ₜ[k₀] pb.gen ∈ C.restrictScalars k₀ :=
      (Subalgebra.mem_restrictScalars k₀).mpr (Algebra.self_mem_adjoin_singleton S _)
    have hle : Algebra.adjoin k₀ {(1 : F) ⊗ₜ[k₀] pb.gen} ≤ C.restrictScalars k₀ :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr hθC)
    apply (Subalgebra.mem_restrictScalars k₀).mp
    apply hle
    apply Polynomial.aeval_mem_adjoin_singleton k₀
  have hψC : ∀ y, ψ y ∈ C := by
    intro y
    induction y using TensorProduct.inductionOn with | tmul l s => rw [hψt']; apply C.mul_mem (C.algebraMap_mem s) (h1L l) | add x y hx hy => rw [map_add]; apply C.add_mem hx hy
  let Rψ : Subalgebra S (F ⊗[k₀] L) :=
    { carrier := Set.range ψ
      mul_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        refine ⟨x * y, map_mul ψ x y⟩
      one_mem' := by
        refine ⟨1, map_one ψ⟩
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        refine ⟨x + y, map_add ψ x y⟩
      zero_mem' := by
        refine ⟨0, map_zero ψ⟩
      algebraMap_mem' := fun s => by
        refine ⟨(1 : L) ⊗ₜ s, ?_⟩
        rw [hψt', ← Algebra.TensorProduct.one_def, mul_one] }
  have hCψ : C ≤ Rψ := by
    refine Algebra.adjoin_le (Set.singleton_subset_iff.mpr ?_)
    refine ⟨pb.gen ⊗ₜ (1 : S), ?_⟩
    rw [hψt', map_one, one_mul]
  let ψC : L ⊗[k₀] S →+* C := (ψ : L ⊗[k₀] S →+* F ⊗[k₀] L).codRestrict C hψC
  have hψCb : Function.Bijective ψC := by
    refine ⟨fun x y hxy => hψ (congrArg Subtype.val hxy), fun c => ?_⟩
    obtain ⟨y, hy⟩ := hCψ c.2
    refine ⟨y, Subtype.ext hy⟩
  let e : L ⊗[k₀] S ≃+* C := RingEquiv.ofBijective ψC hψCb
  let _ : IsIntegrallyClosed C := hIC
  refine ⟨Function.Injective.isDomain (ψ : L ⊗[k₀] S →+* F ⊗[k₀] L) hψ,
    IsIntegrallyClosed.of_equiv e.symm⟩


-- created on 2026-10-13

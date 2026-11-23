module

public import Mathlib
public import Def.DedekindDomain_FiniteAdeleRing_TensorPi
public import Class.Mathlib_Algebra_IsDirectLimit
public import Theorem.Set.Algebra.RestrictedProduct.Basic
public import Instance.DedekindDomain_FiniteAdeleRing_IsDirectLimitRestricted

public section

section

namespace RestrictedProduct

open TensorProduct

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  {ι : Type*} (N : ι → Type*) [∀ i, AddCommGroup (N i)]
  [∀ i, Module R (N i)]

variable (ℱ : Filter ι) (L : ∀ i, Submodule R (N i))


@[simp]
public theorem lTensor_tmul (m : M) (f : Πʳ i, [N i, L i]_[ℱ]) (i : ι) :
    lTensor R M N ℱ L (m ⊗ₜ f) i = m ⊗ₜ (f i) :=
  rfl


@[simp]
public theorem lTensorLeft_tmul (R M : Type*) [CommRing R] [CommRing M] [Algebra R M] {ι : Type*}
    (N : ι → Type*) [∀ i, Ring (N i)] [∀ i, Algebra R (N i)] (L : ∀ i, Submodule R (N i))
    (ℱ : Filter ι) (m : M) (f : Πʳ i, [N i, L i]_[ℱ]) (i : ι) :
    lTensorLeft R M N ℱ L (m ⊗ₜ f) i = m ⊗ₜ (f i) := by
  rw [lTensorLeft, LinearMap.liftBaseChange_tmul, smul_apply, mapAlongLinearMap_apply]
  change m • (_ ⊗ₜ[R] _) = _
  simp [id_eq, smul_tmul' m (1 : M) (f i)]


public theorem coe_lTensorLeft_eq_lTensor (R M : Type*) [CommRing R] [CommRing M] [Algebra R M] {ι : Type*}
    (N : ι → Type*) [∀ i, Ring (N i)] [∀ i, Algebra R (N i)] (L : ∀ i, Submodule R (N i))
    (ℱ : Filter ι) :
    ⇑(lTensorLeft R M N ℱ L) = lTensor R M N ℱ L := by
  ext x i
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, zero_apply]; rfl
  | tmul x y => simp [lTensorLeft_tmul]; rfl
  | add x y hx hy => simp_all; rfl

variable (S : Set ι) [Module.FinitePresentation R M] [Module.Flat R M]


public theorem lTensorPrincipalEquiv_tmul (m : M) (x : Πʳ i, [N i, L i]_[𝓟 S]) (i : ι) :
    lTensorPrincipalEquiv R M N L S (m ⊗ₜ x) i = m ⊗ₜ x i := by
  simp [lTensorPrincipalEquiv, tensorPi_equiv_piTensor'_apply, tmulEquivRangeLTensor,
      rangeLTensor]

set_option backward.isDefEq.respectTransparency false in
open scoped Filter in

public theorem lTensor_bijective : Function.Bijective (lTensor R M N ℱ L) := by
  classical
  let comp1 := TensorProduct.directLimitRight (ι := ℱ.setsᵒᵈ) (fun _ _ x3 ↦ (inclusionLinearMap
    _ _ L <| Filter.monotone_principal x3)) M (R:=R)
  let comp := IsDirectLimit.Module.linearEquiv
    (fun _ _ h ↦ (inclusionLinearMap _ _ L (Filter.monotone_principal h)))
    (fun S ↦ inclusionLinearMap _ _ L <| Filter.le_principal_iff.2 S.2)
    (Module.DirectLimit.of R ℱ.setsᵒᵈ (fun (S : ℱ.setsᵒᵈ) ↦ Πʳ i, [N i, L i]_[𝓟 S.1])
    (fun _ _ x3 ↦ (inclusionLinearMap _ _ L (Filter.monotone_principal x3))) · )
  let comp2 := IsDirectLimit.Module.linearEquiv (fun (_ : ℱ.setsᵒᵈ) _ x3 ↦
      (inclusionLinearMap _ _ _ (Filter.monotone_principal x3)))
    (fun S ↦ inclusionLinearMap _ _ _ <| Filter.le_principal_iff.2 S.2)
    (Module.DirectLimit.of R _
      (fun (S : ℱ.setsᵒᵈ) ↦ Πʳ i, [(M ⊗[R] N i), rangeLTensor R M N L i]_[𝓟 S.1])
      (fun _ _ x3 ↦ (inclusionLinearMap _ _ _ (Filter.monotone_principal x3))) · )
  let comp4 := (LinearEquiv.lTensor M comp) ≪≫ₗ comp1
  let comp5 : Module.DirectLimit
      (fun (S : ℱ.setsᵒᵈ) ↦ M ⊗[R] Πʳ (i : ι), [N i, L i]_[𝓟 S.1])
      (fun i j h ↦
        LinearMap.lTensor M (inclusionLinearMap _ _ _ (Filter.monotone_principal h))) ≃ₗ[R]
      Module.DirectLimit
      (fun (S : ℱ.setsᵒᵈ) ↦ Πʳ (i : ι), [M ⊗[R] N i, (rangeLTensor R M N L i)]_[𝓟 (S.1)])
      (fun _ _ x3 ↦ inclusionLinearMap _ _ _ (Filter.monotone_principal x3)) :=
    Module.DirectLimit.congr (fun (S : ℱ.setsᵒᵈ) ↦
      (RestrictedProduct.lTensorPrincipalEquiv R M N L (S.1 : Set ι))) (by
        intro i j hij
        refine TensorProduct.ext' (fun x y ↦ ?_)
        ext k
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
          LinearMap.lTensor_tmul, lTensorPrincipalEquiv_tmul]
        change x ⊗ₜ[R] y k = ((lTensorPrincipalEquiv R M N L i.1) (x ⊗ₜ[R] y)) k
        rw [lTensorPrincipalEquiv_tmul])
  let tensor_comm' := comp4 ≪≫ₗ comp5 ≪≫ₗ comp2.symm
  have : RestrictedProduct.lTensor R M N ℱ L = tensor_comm' := by
    ext m x i
    simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars, lTensor_tmul, LinearEquiv.coe_coe, tensor_comm', comp2,
      comp4, comp5, comp, comp1, LinearEquiv.trans_apply, LinearEquiv.lTensor_tmul]
    obtain ⟨j, x', hjx'⟩ := Module.DirectLimit.exists_of (comp x)
    rw [← hjx', TensorProduct.directLimitRight_tmul_of, Module.DirectLimit.congr_apply_of]
    simp only [rangeLTensor, lTensorPrincipalEquiv, tmulEquivRangeLTensor,
      LinearEquiv.trans_apply, LinearEquiv.ofInjective_apply, LinearEquiv.trans_symm,
      LinearEquiv.lTensor_tmul, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      tensorPi_equiv_piTensor'_apply, LinearMap.lTensor_tmul, Submodule.subtype_apply,
      LinearEquiv.coe_ofEq_apply, LinearEquiv.ofTop_apply, dite_eq_ite, ite_self,
      IsDirectLimit.Module.linearEquiv_symm_apply, inclusionLinearMap]
    apply_fun comp.symm at hjx'
    simp only [comp, IsDirectLimit.Module.linearEquiv_symm_apply, inclusionLinearMap,
      LinearEquiv.symm_apply_apply, id_eq] at hjx'
    simp only [← congrFun (congrArg DFunLike.coe hjx') i, mapAlongLinearMap_apply, id_eq,
      LinearMap.id_coe]
    rfl
  rw [this]
  exact tensor_comm'.bijective


public theorem lTensorLeft_bijective (R M : Type*) [CommRing R] [CommRing M] [Algebra R M] {ι : Type*}
    (N : ι → Type*) [∀ i, Ring (N i)] [∀ i, Algebra R (N i)] (L : ∀ i, Submodule R (N i))
    (ℱ : Filter ι) [Module.Flat R M] [Module.FinitePresentation R M] :
    Function.Bijective (lTensorLeft R M N ℱ L) := by
  rw [coe_lTensorLeft_eq_lTensor]
  exact lTensor_bijective R M N ℱ L


@[simp]
public theorem lTensorEquiv_tmul (m : M) (f : Πʳ i, [N i, L i]_[ℱ]) (i : ι) :
    lTensorEquiv R M N ℱ L (m ⊗ₜ f) i = m ⊗ₜ (f i) :=
  rfl


@[simp]
public theorem lTensorEquivLeft_tmul (R M : Type*) [CommRing R] [CommRing M] [Algebra R M] {ι : Type*}
    (N : ι → Type*) [∀ i, Ring (N i)] [∀ i, Algebra R (N i)] (L : ∀ i, Submodule R (N i))
    (ℱ : Filter ι) [Module.Flat R M] [Module.FinitePresentation R M] (m : M)
    (f : Πʳ i, [N i, L i]_[ℱ]) (i : ι) :
    lTensorEquivLeft R M N L ℱ (m ⊗ₜ f) i = m ⊗ₜ (f i) := by
  simp [lTensorEquivLeft]

end RestrictedProduct

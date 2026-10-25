import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.TensorReduced
open Algebra TensorProduct


/--
[Algebra.isGeometricallyReduced_of_isAlgClosed_of_isReduced](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TensorReduced.lean)
-/
@[path]
lemma Algebra.isGeometricallyReduced_of_isAlgClosed_of_isReduced
  {k : Type*}
  [Field k]
  [IsAlgClosed k]
  {A : Type*}
  [CommRing A]
  [Algebra k A]
  [IsReduced A] :
-- imply
  Algebra.IsGeometricallyReduced k A := by
-- proof
  constructor
  let φ : AlgebraicClosure k →ₐ[k] k := IsAlgClosed.lift
  let ψ : (AlgebraicClosure k) ⊗[k] A →ₐ[k] A :=
    (Algebra.TensorProduct.lid k A).toAlgHom.comp
      (Algebra.TensorProduct.map φ (AlgHom.id k A))
  apply isReduced_of_injective ψ
  intro x y hxy
  have h1 := (Algebra.TensorProduct.lid k A).injective
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := A)
    (φ.toLinearMap) (RingHom.injective φ.toRingHom)
  apply h2; apply h1; exact hxy
set_option backward.isDefEq.respectTransparency false in

/--
[exists_algHom_ne_zero_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TensorReduced.lean)
-/
@[path]
lemma exists_algHom_ne_zero_of_ne_zero
  {k : Type*}
  [Field k]
  [IsAlgClosed k]
  {A : Type*}
  [CommRing A]
  [Algebra k A]
  [Algebra.FiniteType k A]
  [IsReduced A]
  [Nontrivial A]
  {a : A}
-- given
  (ha : a ≠ 0) :
-- imply
  ∃ φ : A →ₐ[k] k, φ a ≠ 0 := by
-- proof
  haveI : IsJacobsonRing A := @isJacobsonRing_of_finiteType k A _ _ _ _ _
  obtain ⟨m, hm, ham⟩ : ∃ m : Ideal A, m.IsMaximal ∧ a ∉ m := by
    by_contra h; push Not at h
    have hmem : a ∈ (⊥ : Ideal A).jacobson :=
      Ideal.mem_sInf.mpr (fun m ⟨_, hm⟩ => h m hm)
    rw [← Ideal.radical_eq_jacobson] at hmem
    change a ∈ nilradical A at hmem
    rw [nilradical_eq_zero] at hmem
    exact ha hmem
  haveI := hm
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (A ⧸ m) := Algebra.FiniteType.quotient k m
  haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  haveI : Algebra.IsIntegral k (A ⧸ m) := Algebra.IsIntegral.of_finite k (A ⧸ m)
  haveI : Algebra.IsAlgebraic k (A ⧸ m) := Algebra.IsIntegral.isAlgebraic
  let lift : (A ⧸ m) →ₐ[k] k := IsAlgClosed.lift
  use lift.comp (Ideal.Quotient.mkₐ k m)
  intro h
  apply ham
  have : Ideal.Quotient.mkₐ k m a = 0 :=
    (RingHom.injective lift.toRingHom) (by simpa [AlgHom.comp_apply] using h)
  rwa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at this
set_option maxHeartbeats 400000 in

/--
[repr_eval_eq_phi_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TensorReduced.lean)
-/
@[path]
lemma repr_eval_eq_phi_coeff
  [Field k]
  [CommRing A]
  [CommRing B]
  [Algebra k A]
  [Algebra k B]
  [DecidableEq ι]
  {b : Module.Basis ι k B}
  {φ : A →ₐ[k] k}
  {x : A ⊗[k] B}
  {j : ι}
  {tensorIso : A ⊗[k] B ≃ₗ[k] (ι →₀ A)}
-- given
  (htiso : tensorIso = (TensorProduct.congr (LinearEquiv.refl k A) b.repr).trans (TensorProduct.finsuppScalarRight k k A ι)) :
-- imply
  b.repr (((Algebra.TensorProduct.lid k B).toAlgHom.comp (Algebra.TensorProduct.map φ (AlgHom.id k B))) x) j = φ (tensorIso x j) := by
-- proof
  subst htiso
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | tmul a bv =>
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, Algebra.TensorProduct.lid_tmul,
      LinearEquiv.trans_apply, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply, finsuppScalarRight_apply_tmul_apply]
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_smul, smul_eq_mul, mul_comm]
  | add x y ihx ihy =>
    simp only [map_add, Finsupp.add_apply] at ihx ihy ⊢
    rw [ihx, ihy]
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in

/--
[tensorProduct_isReduced_of_isAlgClosed_finiteType](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TensorReduced.lean)
-/
@[path]
lemma tensorProduct_isReduced_of_isAlgClosed_finiteType
  {k : Type*}
  [Field k]
  [IsAlgClosed k]
  {A B : Type*}
  [CommRing A]
  [CommRing B]
  [Algebra k A]
  [Algebra k B]
  [IsReduced A]
  [IsReduced B]
  [Algebra.FiniteType k A] :
-- imply
  IsReduced (A ⊗[k] B) := by
-- proof
  rw [isReduced_iff]
  intro x ⟨n, hxn⟩
  have heval : ∀ φ : A →ₐ[k] k,
    ((Algebra.TensorProduct.lid k B).toAlgHom.comp
      (Algebra.TensorProduct.map φ (AlgHom.id k B))) x = 0 := by
    intro φ
    let ψ := (Algebra.TensorProduct.lid k B).toAlgHom.comp
      (Algebra.TensorProduct.map φ (AlgHom.id k B))
    have hnil : IsNilpotent (ψ x) := ⟨n, by simp [ψ, ← map_pow, hxn, map_zero]⟩
    exact IsReduced.eq_zero _ hnil
  by_cases hA : Nontrivial A
  · let ι := Module.Free.ChooseBasisIndex k B
    let b := Module.Free.chooseBasis k B
    let tensorIso : A ⊗[k] B ≃ₗ[k] (ι →₀ A) :=
      (TensorProduct.congr (LinearEquiv.refl k A) b.repr).trans
        (TensorProduct.finsuppScalarRight k k A ι)
    suffices h : tensorIso x = 0 from tensorIso.injective (h.trans (map_zero _).symm)
    ext i
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hfi
    obtain ⟨φ, hφ⟩ := exists_algHom_ne_zero_of_ne_zero k A hfi
    have h0 := heval φ
    have hkey := repr_eval_eq_phi_coeff b φ x i tensorIso rfl
    rw [h0, map_zero, Finsupp.zero_apply] at hkey
    exact hφ hkey.symm
  · rw [not_nontrivial_iff_subsingleton] at hA
    haveI : Subsingleton (A ⊗[k] B) := Unique.instSubsingleton (α := A ⊗[k] B)
    exact Subsingleton.eq_zero x
set_option backward.isDefEq.respectTransparency false in

/--
[tensor_product_reduced_of_algClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TensorReduced.lean)
-/
@[path]
lemma tensor_product_reduced_of_algClosed
  {k : Type*}
  [Field k]
  [IsAlgClosed k]
  {A : Type*}
  [CommRing A]
  [Algebra k A]
  [IsReduced A]
  {B : Type*}
  [CommRing B]
  [Algebra k B]
  [IsReduced B] :
-- imply
  IsReduced (A ⊗[k] B) := by
-- proof
  suffices h : IsReduced (B ⊗[k] A) by
    exact isReduced_of_injective (Algebra.TensorProduct.comm k A B)
      (Algebra.TensorProduct.comm k A B).injective
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro D hD
  haveI : Algebra.FiniteType k D := D.fg_iff_finiteType.mp hD
  haveI : IsReduced D := isReduced_of_injective (Subalgebra.val D) Subtype.val_injective
  haveI : IsReduced (D ⊗[k] B) := tensorProduct_isReduced_of_isAlgClosed_finiteType k D B
  exact isReduced_of_injective (Algebra.TensorProduct.comm k B D)
    (Algebra.TensorProduct.comm k B D).injective


-- created on 2026-10-23

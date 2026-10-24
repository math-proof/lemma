import Mathlib

set_option autoImplicit false

open scoped TensorProduct

universe u v w x

namespace HopfAlgebra

structure FVectStructure (F : Type w) [Field F] (R : Type u) [CommRing R]
    (H : Type v) [CommRing H] [Bialgebra R H] where

  act : F → (H →ₐc[R] H)

  act_one : act 1 = BialgHom.id R H

  act_mul : ∀ a b : F, act (a * b) = (act a).comp (act b)

  act_zero : WithConv.toConv (act 0 : H →ₐ[R] H) = (1 : WithConv (H →ₐ[R] H))

  act_add : ∀ a b : F, WithConv.toConv (act (a + b) : H →ₐ[R] H) =
    WithConv.toConv (act a : H →ₐ[R] H) * WithConv.toConv (act b : H →ₐ[R] H)

namespace FVectStructure

variable {F : Type w} [Field F] {R : Type u} [CommRing R] {H : Type v} [CommRing H] [Bialgebra R H]
variable (σ : FVectStructure F R H)

noncomputable def addChar : AddChar F (WithConv (H →ₐ[R] H)) where
  toFun a := WithConv.toConv (σ.act a : H →ₐ[R] H)
  map_zero_eq_one' := σ.act_zero
  map_add_eq_mul' := σ.act_add

@[simp] theorem addChar_apply (a : F) : σ.addChar a = WithConv.toConv (σ.act a : H →ₐ[R] H) := rfl

theorem act_add_linearMap (a b : F) :
    ((σ.act (a + b) : H →ₐ[R] H).toLinearMap) =
      LinearMap.mul' R H ∘ₗ TensorProduct.map (σ.act a : H →ₐ[R] H).toLinearMap (σ.act b : H →ₐ[R] H).toLinearMap
        ∘ₗ Coalgebra.comul := by
  have h := σ.act_add a b
  rw [AlgHom.convMul_def] at h
  have h2 := congrArg (fun x => (WithConv.ofConv x).toLinearMap) h
  simpa [TensorProduct.AlgebraTensorModule.map_eq, Algebra.TensorProduct.lmul'_toLinearMap] using h2

theorem toConv_act_nsmul (n : ℕ) (a : F) :
    WithConv.toConv (σ.act (n • a) : H →ₐ[R] H) = WithConv.toConv (σ.act a : H →ₐ[R] H) ^ n := by
  rw [← addChar_apply, ← addChar_apply, AddChar.map_nsmul_eq_pow]

theorem toConv_act_pow_ringChar (a : F) :
    WithConv.toConv (σ.act a : H →ₐ[R] H) ^ ringChar F = 1 := by
  rw [← toConv_act_nsmul, nsmul_eq_mul, ringChar.Nat.cast_ringChar, zero_mul]
  exact σ.act_zero

include σ in

theorem toConv_id_pow_ringChar :
    WithConv.toConv (AlgHom.id R H) ^ ringChar F = (1 : WithConv (H →ₐ[R] H)) := by
  have h := σ.toConv_act_pow_ringChar 1
  rwa [σ.act_one] at h

include σ in

theorem point_pow_ringChar_eq_one (T : Type x) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)) :
    f ^ ringChar F = 1 := by
  have key : ∀ n : ℕ, f ^ n = WithConv.toConv (f.ofConv.comp
      ((WithConv.toConv (AlgHom.id R H) ^ n : WithConv (H →ₐ[R] H))).ofConv) := by
    intro n
    induction n with
    | zero =>
        rw [pow_zero, pow_zero, AlgHom.convOne_def (R := R) (A := T) (C := H),
          AlgHom.convOne_def (R := R) (A := H) (C := H), WithConv.ofConv_toConv, ← AlgHom.comp_assoc]
        congr 1
        ext x
        simp
    | succ n ih =>
        rw [pow_succ, pow_succ, ih, AlgHom.comp_convMul_distrib, WithConv.ofConv_toConv, AlgHom.comp_id,
          WithConv.toConv_ofConv, WithConv.toConv_ofConv]
  rw [key, σ.toConv_id_pow_ringChar, AlgHom.convOne_def (R := R) (A := H) (C := H), WithConv.ofConv_toConv,
    ← AlgHom.comp_assoc, AlgHom.convOne_def (R := R) (A := T) (C := H)]
  congr 1
  ext x
  simp

theorem act_comp_act_inv (a : Fˣ) : (σ.act a).comp (σ.act (a⁻¹ : Fˣ)) = BialgHom.id R H := by
  rw [← σ.act_mul, Units.mul_inv, σ.act_one]

theorem act_inv_comp_act (a : Fˣ) : (σ.act (a⁻¹ : Fˣ)).comp (σ.act a) = BialgHom.id R H := by
  rw [← σ.act_mul, Units.inv_mul, σ.act_one]

noncomputable def unitsAct (a : Fˣ) : H ≃ₐc[R] H :=
  BialgEquiv.ofBialgHom (σ.act a) (σ.act (a⁻¹ : Fˣ)) (σ.act_comp_act_inv a) (σ.act_inv_comp_act a)

@[simp] theorem unitsAct_apply (a : Fˣ) (x : H) : σ.unitsAct a x = σ.act a x := rfl

theorem unitsAct_one : σ.unitsAct 1 = BialgEquiv.refl R H := by
  ext x
  rw [unitsAct_apply, Units.val_one, σ.act_one]
  rfl

theorem unitsAct_mul (a b : Fˣ) : σ.unitsAct (a * b) = (σ.unitsAct b).trans (σ.unitsAct a) := by
  ext x
  rw [unitsAct_apply, Units.val_mul, σ.act_mul]
  rfl

end FVectStructure

def IsFCompatible {F : Type w} [Field F] {R : Type u} [CommRing R]
    {H : Type v} [CommRing H] [Bialgebra R H] {H' : Type x} [CommRing H'] [Bialgebra R H']
    (σ : FVectStructure F R H) (σ' : FVectStructure F R H') (u : H →ₐc[R] H') : Prop :=
  ∀ a : F, u.comp (σ.act a) = (σ'.act a).comp u

namespace IsFCompatible

variable {F : Type w} [Field F] {R : Type u} [CommRing R]
    {H : Type v} [CommRing H] [Bialgebra R H] {H' : Type x} [CommRing H'] [Bialgebra R H']
    {H'' : Type*} [CommRing H''] [Bialgebra R H'']

theorem id (σ : FVectStructure F R H) : IsFCompatible σ σ (BialgHom.id R H) := by
  intro a; rfl

theorem comp {σ : FVectStructure F R H} {σ' : FVectStructure F R H'} {σ'' : FVectStructure F R H''}
    {v : H' →ₐc[R] H''} {u : H →ₐc[R] H'} (hv : IsFCompatible σ' σ'' v) (hu : IsFCompatible σ σ' u) :
    IsFCompatible σ σ'' (v.comp u) := by
  intro a
  rw [BialgHom.comp_assoc, hu a, ← BialgHom.comp_assoc, hv a, BialgHom.comp_assoc]

theorem apply {σ : FVectStructure F R H} {σ' : FVectStructure F R H'} {u : H →ₐc[R] H'}
    (hu : IsFCompatible σ σ' u) (a : F) (x : H) : u (σ.act a x) = σ'.act a (u x) :=
  DFunLike.congr_fun (hu a) x

end IsFCompatible

namespace FVectStructure

variable (F : Type w) [Field F] (R : Type u) [CommRing R]

noncomputable def addMonoidAlgebra : FVectStructure F R (AddMonoidAlgebra R F) where
  act a := AddMonoidAlgebra.mapDomainBialgHom R (AddMonoidHom.mulLeft a)
  act_one := by
    apply BialgHom.coe_algHom_injective
    refine AddMonoidAlgebra.algHom_ext (fun x => ?_) (Subsingleton.elim _ _)
    simp
  act_mul a b := by
    apply BialgHom.coe_algHom_injective
    refine AddMonoidAlgebra.algHom_ext (fun x => ?_) (Subsingleton.elim _ _)
    simp [mul_assoc]
  act_zero := by
    congr 1
    refine AddMonoidAlgebra.algHom_ext (fun x => ?_) (Subsingleton.elim _ _)
    simp
  act_add a b := by
    rw [AlgHom.convMul_def]
    congr 1
    refine AddMonoidAlgebra.algHom_ext (fun x => ?_) (Subsingleton.elim _ _)
    simp [AddMonoidAlgebra.single_mul_single, add_mul]

end FVectStructure

end HopfAlgebra

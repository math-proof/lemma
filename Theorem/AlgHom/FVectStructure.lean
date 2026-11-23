module

public import Mathlib
public import Structure.HopfAlgebra_FVectStructure

public section

set_option autoImplicit false

open scoped TensorProduct

universe u v w x

namespace HopfAlgebra


namespace FVectStructure

variable {F : Type w} [Field F] {R : Type u} [CommRing R] {H : Type v} [CommRing H] [Bialgebra R H]
variable (σ : FVectStructure F R H)


@[simp] public theorem addChar_apply (a : F) : σ.addChar a = WithConv.toConv (σ.act a : H →ₐ[R] H) := rfl


public theorem act_add_linearMap (a b : F) :
    ((σ.act (a + b) : H →ₐ[R] H).toLinearMap) =
      LinearMap.mul' R H ∘ₗ TensorProduct.map (σ.act a : H →ₐ[R] H).toLinearMap (σ.act b : H →ₐ[R] H).toLinearMap
        ∘ₗ Coalgebra.comul := by
  have h := σ.act_add a b
  rw [AlgHom.convMul_def] at h
  have h2 := congrArg (fun x => (WithConv.ofConv x).toLinearMap) h
  simpa [TensorProduct.AlgebraTensorModule.map_eq, Algebra.TensorProduct.lmul'_toLinearMap] using h2


public theorem toConv_act_nsmul (n : ℕ) (a : F) :
    WithConv.toConv (σ.act (n • a) : H →ₐ[R] H) = WithConv.toConv (σ.act a : H →ₐ[R] H) ^ n := by
  rw [← addChar_apply, ← addChar_apply, AddChar.map_nsmul_eq_pow]


public theorem toConv_act_pow_ringChar (a : F) :
    WithConv.toConv (σ.act a : H →ₐ[R] H) ^ ringChar F = 1 := by
  rw [← toConv_act_nsmul, nsmul_eq_mul, ringChar.Nat.cast_ringChar, zero_mul]
  exact σ.act_zero

include σ in


public theorem toConv_id_pow_ringChar :
    WithConv.toConv (AlgHom.id R H) ^ ringChar F = (1 : WithConv (H →ₐ[R] H)) := by
  have h := σ.toConv_act_pow_ringChar 1
  rwa [σ.act_one] at h

include σ in


public theorem point_pow_ringChar_eq_one (T : Type x) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)) :
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


public theorem act_comp_act_inv (a : Fˣ) : (σ.act a).comp (σ.act (a⁻¹ : Fˣ)) = BialgHom.id R H := by
  rw [← σ.act_mul, Units.mul_inv, σ.act_one]


public theorem act_inv_comp_act (a : Fˣ) : (σ.act (a⁻¹ : Fˣ)).comp (σ.act a) = BialgHom.id R H := by
  rw [← σ.act_mul, Units.inv_mul, σ.act_one]


@[simp] public theorem unitsAct_apply (a : Fˣ) (x : H) : σ.unitsAct a x = σ.act a x := rfl


public theorem unitsAct_one : σ.unitsAct 1 = BialgEquiv.refl R H := by
  ext x
  rw [unitsAct_apply, Units.val_one, σ.act_one]
  rfl


public theorem unitsAct_mul (a b : Fˣ) : σ.unitsAct (a * b) = (σ.unitsAct b).trans (σ.unitsAct a) := by
  ext x
  rw [unitsAct_apply, Units.val_mul, σ.act_mul]
  rfl

end FVectStructure


public theorem id (σ : FVectStructure F R H) : IsFCompatible σ σ (BialgHom.id R H) := by
  intro a; rfl


public theorem comp {σ : FVectStructure F R H} {σ' : FVectStructure F R H'} {σ'' : FVectStructure F R H''}
    {v : H' →ₐc[R] H''} {u : H →ₐc[R] H'} (hv : IsFCompatible σ' σ'' v) (hu : IsFCompatible σ σ' u) :
    IsFCompatible σ σ'' (v.comp u) := by
  intro a
  rw [BialgHom.comp_assoc, hu a, ← BialgHom.comp_assoc, hv a, BialgHom.comp_assoc]


public theorem apply {σ : FVectStructure F R H} {σ' : FVectStructure F R H'} {u : H →ₐc[R] H'}
    (hu : IsFCompatible σ σ' u) (a : F) (x : H) : u (σ.act a x) = σ'.act a (u x) :=
  DFunLike.congr_fun (hu a) x

end IsFCompatible

namespace FVectStructure

variable (F : Type w) [Field F] (R : Type u) [CommRing R]


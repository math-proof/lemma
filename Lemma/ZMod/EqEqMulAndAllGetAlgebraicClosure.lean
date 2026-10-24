import Mathlib
import sympy.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private abbrev γ (n : ℕ) : Multiplicative (ZMod n) := Multiplicative.ofAdd (1 : ZMod n)
private lemma γ_pow_n (n : ℕ) : (γ n) ^ n = 1 := by
  rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, ofAdd_zero]
private lemma γ_pow_val (n : ℕ) [NeZero n] (g : Multiplicative (ZMod n)) : (γ n) ^ (Multiplicative.toAdd g).val = g := by
  rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_val, ZMod.cast_id', id_eq, ofAdd_toAdd]
private lemma val_pow_eq_one (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n] (f : WithConv ((MonoidAlgebra K (Multiplicative (ZMod n))) →ₐ[K] AlgebraicClosure K)) : (f (MonoidAlgebra.of K (Multiplicative (ZMod n)) (γ n))) ^ n = 1 := by
  rw [← map_pow, ← map_pow, γ_pow_n, map_one, map_one]
private lemma val_ne_zero (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n] (f : WithConv ((MonoidAlgebra K (Multiplicative (ZMod n))) →ₐ[K] AlgebraicClosure K)) : f (MonoidAlgebra.of K (Multiplicative (ZMod n)) (γ n)) ≠ 0 := fun h => by
  have := val_pow_eq_one K n f
  rw [h, zero_pow (NeZero.ne n)] at this
  apply one_ne_zero this.symm
private noncomputable def toRoot (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n] (f : WithConv ((MonoidAlgebra K (Multiplicative (ZMod n))) →ₐ[K] AlgebraicClosure K)) : rootsOfUnity n (AlgebraicClosure K) :=
  ⟨Units.mk0 _ (val_ne_zero K n f), by
    rw [mem_rootsOfUnity]
    ext
    push_cast
    apply val_pow_eq_one K n f⟩
private lemma toRoot_coe (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n] (f : WithConv ((MonoidAlgebra K (Multiplicative (ZMod n))) →ₐ[K] AlgebraicClosure K)) : ((toRoot K n f : Units (AlgebraicClosure K)) : AlgebraicClosure K) = f (MonoidAlgebra.of K (Multiplicative (ZMod n)) (γ n)) := rfl
private lemma convMul_of (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n] (f g : WithConv ((MonoidAlgebra K (Multiplicative (ZMod n))) →ₐ[K] AlgebraicClosure K)) (x : Multiplicative (ZMod n)) : (f * g) (MonoidAlgebra.of K (Multiplicative (ZMod n)) x) = f (MonoidAlgebra.of K (Multiplicative (ZMod n)) x) * g (MonoidAlgebra.of K (Multiplicative (ZMod n)) x) := by
  show (f * g).ofConv _ = f.ofConv _ * g.ofConv _
  rw [AlgHom.convMul_apply, MonoidAlgebra.of_apply, MonoidAlgebra.comul_single]
  have h1 : CoalgebraStruct.comul (R := K) (1 : K) = (1 : K) ⊗ₜ[K] (1 : K) := by simp [CoalgebraStruct.comul]
  rw [h1, TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul]
  rfl
private lemma toRoot_mul (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n] (f g : WithConv ((MonoidAlgebra K (Multiplicative (ZMod n))) →ₐ[K] AlgebraicClosure K)) : toRoot K n (f * g) = toRoot K n f * toRoot K n g := by
  refine Subtype.ext (Units.ext ?_)
  push_cast
  apply convMul_of K n f g (γ n)
private lemma toRoot_gal (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n] (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (f g : WithConv ((MonoidAlgebra K (Multiplicative (ZMod n))) →ₐ[K] AlgebraicClosure K)) (hfg : ∀ a, g a = σ (f a)) : ((toRoot K n g : Units (AlgebraicClosure K)) : AlgebraicClosure K) = σ ((toRoot K n f : Units (AlgebraicClosure K)) : AlgebraicClosure K) := by
  rw [toRoot_coe, toRoot_coe]
  apply hfg _
private lemma toRoot_injective (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n] : Function.Injective (toRoot K n) := by
  intro f g h
  have hval : f (MonoidAlgebra.of K (Multiplicative (ZMod n)) (γ n)) = g (MonoidAlgebra.of K (Multiplicative (ZMod n)) (γ n)) := by
    have hh : ((toRoot K n f : Units (AlgebraicClosure K)) : AlgebraicClosure K) = ((toRoot K n g : Units (AlgebraicClosure K)) : AlgebraicClosure K) := by rw [h]
    rwa [toRoot_coe, toRoot_coe] at hh
  have hof : f.ofConv = g.ofConv := by
    apply (MonoidAlgebra.lift K (AlgebraicClosure K) (Multiplicative (ZMod n))).symm.injective
    refine MonoidHom.ext fun x => ?_
    rw [MonoidAlgebra.lift_symm_apply, MonoidAlgebra.lift_symm_apply]
    show f (MonoidAlgebra.of K (Multiplicative (ZMod n)) x) = g (MonoidAlgebra.of K (Multiplicative (ZMod n)) x)
    rw [← γ_pow_val n x]
    simp only [map_pow]
    apply congrArg (· ^ (Multiplicative.toAdd x).val) hval
  calc
    _ = WithConv.toConv f.ofConv := rfl
    _ = WithConv.toConv g.ofConv := by rw [hof]
    _ = g := rfl
private noncomputable def rootHom (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n] (ζ : Units (AlgebraicClosure K)) (hζ : ζ ^ n = 1) : Multiplicative (ZMod n) →* Units (AlgebraicClosure K) where
  toFun g := ζ ^ (Multiplicative.toAdd g).val
  map_one' := by simp
  map_mul' a b := by
    have hζpow : ∀ m : ℕ, ζ ^ m = ζ ^ (m % n) := fun m => by
      conv_lhs => rw [← Nat.mod_add_div m n, pow_add, pow_mul, hζ, one_pow, mul_one]
    simp only [toAdd_mul]
    rw [ZMod.val_add, ← hζpow, pow_add]
private lemma rootHom_γ (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n] (ζ : Units (AlgebraicClosure K)) (hζ : ζ ^ n = 1) : rootHom K n ζ hζ (γ n) = ζ := by
  show ζ ^ (Multiplicative.toAdd (γ n)).val = ζ
  have hv : (Multiplicative.toAdd (γ n)).val = 1 % n := by
    rw [show Multiplicative.toAdd (γ n) = (1 : ZMod n) from rfl, show (1 : ZMod n) = ((1 : ℕ) : ZMod n) from (Nat.cast_one (R := ZMod n)).symm, ZMod.val_natCast]
  have hζpow : ∀ m : ℕ, ζ ^ (m % n) = ζ ^ m := fun m => by
    conv_rhs => rw [← Nat.mod_add_div m n, pow_add, pow_mul, hζ, one_pow, mul_one]
  rw [hv, hζpow 1, pow_one]
private noncomputable def fromRoot (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n] (ζ : rootsOfUnity n (AlgebraicClosure K)) : WithConv ((MonoidAlgebra K (Multiplicative (ZMod n))) →ₐ[K] AlgebraicClosure K) :=
  WithConv.toConv <| (MonoidAlgebra.lift K (AlgebraicClosure K) (Multiplicative (ZMod n))) <| (Units.coeHom (AlgebraicClosure K)).comp (rootHom K n (ζ : Units (AlgebraicClosure K)) ((mem_rootsOfUnity ..).mp ζ.2))
private lemma fromRoot_val (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n] (ζ : rootsOfUnity n (AlgebraicClosure K)) : (fromRoot K n ζ) (MonoidAlgebra.of K (Multiplicative (ZMod n)) (γ n)) = ((ζ : Units (AlgebraicClosure K)) : AlgebraicClosure K) := by
  show ((MonoidAlgebra.lift K (AlgebraicClosure K) (Multiplicative (ZMod n))) _) (MonoidAlgebra.of K (Multiplicative (ZMod n)) (γ n)) = _
  rw [show (MonoidAlgebra.of K (Multiplicative (ZMod n)) (γ n)) = MonoidAlgebra.single (γ n) 1 from rfl, ← MonoidAlgebra.lift_symm_apply, Equiv.symm_apply_apply]
  simp only [MonoidHom.comp_apply, Units.coeHom_apply]
  rw [rootHom_γ]
private lemma toRoot_fromRoot (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n] (ζ : rootsOfUnity n (AlgebraicClosure K)) : toRoot K n (fromRoot K n ζ) = ζ := by
  refine Subtype.ext (Units.ext ?_)
  rw [toRoot_coe, fromRoot_val]
private lemma toRoot_surjective (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n] : Function.Surjective (toRoot K n) :=
  fun ζ => ⟨fromRoot K n ζ, toRoot_fromRoot K n ζ⟩
/--
[MonoidAlgebra_exists_equiv_withConv_algHom_rootsOfUnity_zmod](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MonoidAlgebra_exists_equiv_withConv_algHom_rootsOfUnity_zmod.lean)
-/
@[path]
private lemma main
  (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n] :
  -- imply
  ∃ eμ : WithConv ((MonoidAlgebra K (Multiplicative (ZMod n))) →ₐ[K] AlgebraicClosure K) ≃ rootsOfUnity n (AlgebraicClosure K), (∀ f g, eμ (f * g) = eμ f * eμ g) ∧ ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) f g, (∀ a, g a = σ (f a)) → ((eμ g : Units (AlgebraicClosure K)) : AlgebraicClosure K) = σ ((eμ f : Units (AlgebraicClosure K)) : AlgebraicClosure K) :=
  ⟨Equiv.ofBijective (toRoot K n) ⟨toRoot_injective K n, toRoot_surjective K n⟩, toRoot_mul K n, toRoot_gal K n⟩


-- created on 2026-10-20

import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R] (k : Type) [CommRing k] [Algebra R k]
  (H : Type) [CommRing H] [Bialgebra R H]
private noncomputable def beta0 : WithConv (H →ₐ[R] DualNumber k) ≃ (k ⊗[R] H →ₐ[k] DualNumber k) :=
  (WithConv.equiv (H →ₐ[R] DualNumber k)).trans (AlgHom.liftEquiv R k H (DualNumber k))
private lemma beta0_tmul (D : WithConv (H →ₐ[R] DualNumber k)) (s : k) (h : H) :
    beta0 R k H D (s ⊗ₜ[R] h) = s • D.ofConv h := rfl
private lemma beta0_one_tmul (D : WithConv (H →ₐ[R] DualNumber k)) (h : H) :
    beta0 R k H D ((1 : k) ⊗ₜ[R] h) = D.ofConv h := by
  rw [beta0_tmul, one_smul]
private lemma over_counit_iff (D : WithConv (H →ₐ[R] DualNumber k)) :
    (∀ h : H, TrivSqZeroExt.fst (D.ofConv h) = algebraMap R k (Bialgebra.counitAlgHom R H h)) ↔
    ∀ b : k ⊗[R] H, TrivSqZeroExt.fst (beta0 R k H D b) = Bialgebra.counitAlgHom k (k ⊗[R] H) b := by
  constructor
  · intro hD b
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul s h =>
        rw [beta0_tmul, TrivSqZeroExt.fst_smul, hD h]
        simp only [Bialgebra.counitAlgHom_apply]
        rw [TensorProduct.counit_tmul, CommSemiring.counit_apply, smul_eq_mul, Algebra.smul_def, mul_comm]
    | add x y hx hy => rw [map_add, TrivSqZeroExt.fst_add, hx, hy, map_add]
  · intro hD h
    have := hD ((1 : k) ⊗ₜ[R] h)
    rw [beta0_one_tmul, Bialgebra.counitAlgHom_apply, TensorProduct.counit_tmul,
      CommSemiring.counit_apply] at this
    rw [this, Bialgebra.counitAlgHom_apply, Algebra.smul_def, mul_one]
private noncomputable def beta :
    {D : WithConv (H →ₐ[R] DualNumber k) //
        ∀ h : H, TrivSqZeroExt.fst (D.ofConv h) = algebraMap R k (Bialgebra.counitAlgHom R H h)} ≃
      {D : k ⊗[R] H →ₐ[k] DualNumber k //
        ∀ b : k ⊗[R] H, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k (k ⊗[R] H) b} :=
  (beta0 R k H).subtypeEquiv (over_counit_iff R k H)
/--
[Bialgebra_exists_equiv_withConv_algHom_dualNumber_over_counit_baseChange_apply_one_tmul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Bialgebra_exists_equiv_withConv_algHom_dualNumber_over_counit_baseChange_apply_one_tmul.lean)
-/
@[path]
private lemma main
    (R : Type) [CommRing R] (k : Type) [CommRing k] [Algebra R k]
    (H : Type) [CommRing H] [Bialgebra R H] :
    ∃ β : {D : WithConv (H →ₐ[R] DualNumber k) //
            ∀ h : H, TrivSqZeroExt.fst (D.ofConv h) = algebraMap R k (Bialgebra.counitAlgHom R H h)} ≃
          {D : k ⊗[R] H →ₐ[k] DualNumber k //
            ∀ b : k ⊗[R] H, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k (k ⊗[R] H) b},
      ∀ (D : {D : WithConv (H →ₐ[R] DualNumber k) //
            ∀ h : H, TrivSqZeroExt.fst (D.ofConv h) = algebraMap R k (Bialgebra.counitAlgHom R H h)})
        (h : H), (β D).1 ((1 : k) ⊗ₜ[R] h) = D.1.ofConv h :=
  ⟨beta R k H, fun D h => beta0_one_tmul R k H D.1 h⟩

-- created on 2026-10-20

import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


variable (R : Type) [CommRing R] (k : Type) [CommRing k] [Algebra R k]
variable (H : Type) [CommRing H] [Bialgebra R H]

private noncomputable def beta0 : WithConv (AlgHom R H (DualNumber k)) ≃ AlgHom k (TensorProduct R k H) (DualNumber k) :=
  (WithConv.equiv (AlgHom R H (DualNumber k))).trans (AlgHom.liftEquiv R k H (DualNumber k))

private lemma beta0_tmul (D : WithConv (AlgHom R H (DualNumber k))) (s : k) (h : H) :
  -- imply
  beta0 R k H D (TensorProduct.tmul R s h) = s • D.ofConv h := rfl

private lemma beta0_one_tmul (D : WithConv (AlgHom R H (DualNumber k))) (h : H) :
  -- imply
  beta0 R k H D (TensorProduct.tmul R (1 : k) h) = D.ofConv h := by
  -- proof
  rw [beta0_tmul, one_smul]

private lemma over_counit_iff (D : WithConv (AlgHom R H (DualNumber k))) :
  -- imply
  (∀ h : H, TrivSqZeroExt.fst (D.ofConv h) = algebraMap R k (Bialgebra.counitAlgHom R H h)) ↔ ∀ b : TensorProduct R k H, TrivSqZeroExt.fst (beta0 R k H D b) = Bialgebra.counitAlgHom k (TensorProduct R k H) b := by
  -- proof
  constructor
  ·
    intro hD b
    induction b using TensorProduct.inductionOn with
    | tmul s h =>
      rw [beta0_tmul, TrivSqZeroExt.fst_smul, hD h]
      simp [Bialgebra.counitAlgHom_apply]
      rw [Algebra.smul_def, mul_comm]
    | add x y hx hy =>
      rw [map_add, TrivSqZeroExt.fst_add, hx, hy, map_add]
  ·
    intro hD h
    have hβ := hD (TensorProduct.tmul R (1 : k) h)
    rw [beta0_one_tmul, Bialgebra.counitAlgHom_apply, TensorProduct.counit_tmul, CommSemiring.counit_apply] at hβ
    rw [hβ, Bialgebra.counitAlgHom_apply, Algebra.smul_def, mul_one]

private def OverCounit :=
  Subtype fun D : WithConv (AlgHom R H (DualNumber k)) => ∀ h : H, TrivSqZeroExt.fst (WithConv.ofConv D h) = algebraMap R k (Bialgebra.counitAlgHom R H h)

private def OverCounitTensor :=
  Subtype fun D : AlgHom k (TensorProduct R k H) (DualNumber k) => ∀ b : TensorProduct R k H, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k (TensorProduct R k H) b

private noncomputable def beta : OverCounit R k H ≃ OverCounitTensor R k H :=
  (beta0 R k H).subtypeEquiv (over_counit_iff R k H)

/--
[Bialgebra_exists_equiv_withConv_algHom_dualNumber_over_counit_baseChange_apply_one_tmul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Bialgebra_exists_equiv_withConv_algHom_dualNumber_over_counit_baseChange_apply_one_tmul.lean)
-/
@[path]
private lemma main
  (R : Type) [CommRing R] (k : Type) [CommRing k] [Algebra R k]
  (H : Type) [CommRing H] [Bialgebra R H] :
  -- imply
  ∃ β : OverCounit R k H ≃ OverCounitTensor R k H, ∀ D h, (β D).val (TensorProduct.tmul R (1 : k) h) = WithConv.ofConv D.val h :=
  ⟨beta R k H, fun D h => beta0_one_tmul R k H D.val h⟩


-- created on 2026-10-20

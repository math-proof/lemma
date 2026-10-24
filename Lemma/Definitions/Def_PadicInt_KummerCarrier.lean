import Mathlib

open scoped TensorProduct
open Polynomial

namespace PadicInt.KummerCarrier

variable (p : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ)

noncomputable abbrev kpoly (j : ZMod p) : ℤ_[p][X] := X ^ p - C ((u : ℤ_[p]) ^ j.val)

lemma kpoly_monic (j : ZMod p) : (kpoly p u j).Monic :=
  (monic_X_pow p).sub_of_left <| by
    apply lt_of_le_of_lt degree_C_le
    rw [degree_X_pow]; exact_mod_cast (Fact.out : p.Prime).pos

noncomputable abbrev A (j : ZMod p) := AdjoinRoot (kpoly p u j)

noncomputable instance (j : ZMod p) : Module.Free ℤ_[p] (A p u j) :=
  (kpoly_monic p u j).free_adjoinRoot
noncomputable instance (j : ZMod p) : Module.Finite ℤ_[p] (A p u j) :=
  (kpoly_monic p u j).finite_adjoinRoot

noncomputable abbrev Carrier := Π j : ZMod p, A p u j

noncomputable abbrev z (j : ZMod p) : A p u j := AdjoinRoot.root (kpoly p u j)

lemma z_pow_p (j : ZMod p) :
    z p u j ^ p = algebraMap ℤ_[p] (A p u j) ((u : ℤ_[p]) ^ j.val) := by
  have h : (Polynomial.aeval (z p u j)) (kpoly p u j) = 0 := by
    rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_self
  rw [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h
  exact h

noncomputable def ε : Carrier p u →ₐ[ℤ_[p]] ℤ_[p] :=
  (AdjoinRoot.liftAlgHom (kpoly p u 0) (Algebra.ofId ℤ_[p] ℤ_[p]) 1
    (by simp [kpoly, ZMod.val_zero, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C])).comp
    (Pi.evalAlgHom _ _ 0)

noncomputable def piPiEquiv :
    Carrier p u ⊗[ℤ_[p]] Carrier p u ≃ₐ[ℤ_[p]]
      Π a : ZMod p, Π b : ZMod p, A p u a ⊗[ℤ_[p]] A p u b :=
  (Algebra.TensorProduct.comm ℤ_[p] _ _).trans <|
    (Algebra.TensorProduct.piRight ℤ_[p] ℤ_[p] (Carrier p u) (A p u)).trans <|
      AlgEquiv.piCongrRight fun a =>
        (Algebra.TensorProduct.comm ℤ_[p] _ _).trans <|
          Algebra.TensorProduct.piRight ℤ_[p] ℤ_[p] (A p u a) (A p u)

lemma piPiEquiv_tmul (f g : Carrier p u) (a b : ZMod p) :
    piPiEquiv p u (f ⊗ₜ g) a b = f a ⊗ₜ g b := by
  simp [piPiEquiv, Algebra.TensorProduct.piRight_tmul, Algebra.TensorProduct.comm_tmul]

noncomputable def cfac (a b : ZMod p) : ℤ_[p] := ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) ^ ((a.val + b.val) / p)

lemma cfac_pow_p_mul (a b : ZMod p) :
    cfac p u a b ^ p * (u : ℤ_[p]) ^ (a.val + b.val) = (u : ℤ_[p]) ^ (a + b).val := by
  unfold cfac
  rw [ZMod.val_add, ← pow_mul, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
    ← Units.val_pow_eq_pow_val, ← Units.val_mul]
  congr 1
  rw [← zpow_natCast u, ← zpow_natCast u, ← zpow_natCast u⁻¹, inv_zpow, ← zpow_neg, ← zpow_add]
  congr 1
  have hmd := Nat.mod_add_div (a.val + b.val) p
  have hmc : (a.val + b.val) / p * p = p * ((a.val + b.val) / p) := Nat.mul_comm _ _
  omega

noncomputable def μ (a b : ZMod p) : Carrier p u →ₐ[ℤ_[p]] A p u a ⊗[ℤ_[p]] A p u b :=
  (AdjoinRoot.liftAlgHom (kpoly p u (a + b)) (Algebra.ofId _ _)
    (cfac p u a b • (z p u a ⊗ₜ z p u b))
    (by
      simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
        _root_.smul_pow, Algebra.TensorProduct.tmul_pow, z_pow_p]
      rw [Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u a),
        Algebra.algebraMap_eq_smul_one (R := ℤ_[p]) (A := A p u b),
        TensorProduct.smul_tmul_smul, smul_smul, ← pow_add, cfac_pow_p_mul,
        ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
      rfl)).comp
    (Pi.evalAlgHom _ _ (a + b))

noncomputable def Δ : Carrier p u →ₐ[ℤ_[p]] Carrier p u ⊗[ℤ_[p]] Carrier p u :=
  (piPiEquiv p u).symm.toAlgHom.comp
    (Pi.algHom _ _ fun a => Pi.algHom _ _ fun b => μ p u a b)

variable {L : Type*} [CommRing L] [Algebra ℤ_[p] L]

noncomputable def evalAt (j : ZMod p) (w : L)
    (hw : w ^ p = algebraMap ℤ_[p] L ((u : ℤ_[p]) ^ j.val)) :
    Carrier p u →ₐ[ℤ_[p]] L :=
  (AdjoinRoot.liftAlgHom (kpoly p u j) (Algebra.ofId ℤ_[p] L) w
    (by
      simp only [kpoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero]
      exact hw.trans rfl)).comp
    (Pi.evalAlgHom _ _ j)

noncomputable def polyLift (h : Carrier p u) (j : ZMod p) : Polynomial ℤ_[p] :=
  AdjoinRoot.modByMonicHom (kpoly_monic p u j) (h j)

lemma evalAt_eq_aeval_polyLift (j : ZMod p) (w : L)
    (hw : w ^ p = algebraMap ℤ_[p] L ((u : ℤ_[p]) ^ j.val)) (h : Carrier p u) :
    evalAt p u j w hw h = Polynomial.aeval w (polyLift p u h j) := by
  unfold evalAt polyLift
  simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply]
  conv_lhs => rw [show (h j) = AdjoinRoot.mk _
    (AdjoinRoot.modByMonicHom (kpoly_monic p u j) (h j)) from
    (AdjoinRoot.mk_leftInverse (kpoly_monic p u j) (h j)).symm]
  rw [AdjoinRoot.liftAlgHom_mk]
  rfl

end PadicInt.KummerCarrier

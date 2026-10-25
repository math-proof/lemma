-- Carved from Lemma/Definitions/Def_EllipticCurve_TateModule.lean: instance decls only.
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Def.GaloisRep_Adic
import Lemma.EllipticCurve.TateModule

open IsLocalRing

namespace TateModule

variable {p : ℕ} {M : Type} [AddCommGroup M]

variable [Fact p.Prime]

noncomputable instance instSMul : SMul ℤ_[p] (TateModule p M) :=
  ⟨fun a x => ⟨fun n => ((a.appr n : ℕ) : ℤ) • (x : ℕ → M) n, fun n =>
    ⟨by rw [smul_comm, torsion, smul_zero], by rw [smul_comm, compat, appr_succ_smul_eq]⟩⟩⟩

noncomputable instance instModule : Module ℤ_[p] (TateModule p M) where
  one_smul x := by
    refine Subtype.ext (funext fun n => ?_)
    rw [smul_apply]
    have h : (((1 : ℤ_[p]).appr n : ℕ) : ZMod (p ^ n)) = ((1 : ℕ) : ZMod (p ^ n)) := by
      rw [← toZModPow_eq_appr, map_one, Nat.cast_one]
    rw [natCast_smul_eq_of_zmod_eq (torsion x n) h, Nat.cast_one, one_smul]
  mul_smul a b x := by
    refine Subtype.ext (funext fun n => ?_)
    rw [smul_apply, smul_apply, smul_apply, smul_smul, ← Nat.cast_mul]
    refine natCast_smul_eq_of_zmod_eq (torsion x n) ?_
    rw [← toZModPow_eq_appr, map_mul, toZModPow_eq_appr, toZModPow_eq_appr, Nat.cast_mul]
  smul_zero a := Subtype.ext (funext fun n => by rw [smul_apply, coe_zero, Pi.zero_apply, smul_zero])
  smul_add a x y := Subtype.ext (funext fun n => by
    rw [smul_apply, coe_add, Pi.add_apply, smul_add, coe_add, Pi.add_apply, smul_apply, smul_apply])
  add_smul a b x := by
    refine Subtype.ext (funext fun n => ?_)
    rw [smul_apply, coe_add, Pi.add_apply, smul_apply, smul_apply, ← add_smul, ← Nat.cast_add]
    refine natCast_smul_eq_of_zmod_eq (torsion x n) ?_
    rw [← toZModPow_eq_appr, map_add, toZModPow_eq_appr, toZModPow_eq_appr, Nat.cast_add]
  zero_smul x := by
    refine Subtype.ext (funext fun n => ?_)
    rw [smul_apply, coe_zero, Pi.zero_apply]
    have h : (((0 : ℤ_[p]).appr n : ℕ) : ZMod (p ^ n)) = ((0 : ℕ) : ZMod (p ^ n)) := by
      rw [← toZModPow_eq_appr, map_zero, Nat.cast_zero]
    rw [natCast_smul_eq_of_zmod_eq (torsion x n) h, Nat.cast_zero, zero_smul]


end TateModule



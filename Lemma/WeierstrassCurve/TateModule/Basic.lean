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

def TateModule (p : ℕ) (M : Type) [AddCommGroup M] : AddSubgroup (ℕ → M) where
  carrier := {x | ∀ n, ((p ^ n : ℕ) : ℤ) • x n = 0 ∧ ((p : ℕ) : ℤ) • x (n + 1) = x n}
  add_mem' := fun {x y} hx hy n =>
    ⟨by rw [Pi.add_apply, smul_add, (hx n).1, (hy n).1, add_zero],
     by rw [Pi.add_apply, Pi.add_apply, smul_add, (hx n).2, (hy n).2]⟩
  zero_mem' := fun n => ⟨smul_zero _, by rw [Pi.zero_apply, Pi.zero_apply, smul_zero]⟩
  neg_mem' := fun {x} hx n =>
    ⟨by rw [Pi.neg_apply, smul_neg, (hx n).1, neg_zero],
     by rw [Pi.neg_apply, Pi.neg_apply, smul_neg, (hx n).2]⟩

namespace TateModule

variable {p : ℕ} {M : Type} [AddCommGroup M]

theorem torsion (x : TateModule p M) (n : ℕ) : ((p ^ n : ℕ) : ℤ) • (x : ℕ → M) n = 0 := (x.2 n).1

theorem compat (x : TateModule p M) (n : ℕ) : ((p : ℕ) : ℤ) • (x : ℕ → M) (n + 1) = (x : ℕ → M) n :=
  (x.2 n).2

@[simp] theorem coe_add (x y : TateModule p M) : ((x + y : TateModule p M) : ℕ → M) = x + y := rfl
@[simp] theorem coe_zero : ((0 : TateModule p M) : ℕ → M) = 0 := rfl
@[simp] theorem coe_neg (x : TateModule p M) : ((-x : TateModule p M) : ℕ → M) = -x := rfl
@[simp] theorem coe_sub (x y : TateModule p M) : ((x - y : TateModule p M) : ℕ → M) = x - y := rfl

theorem natCast_smul_eq_mod {n c : ℕ} {m : M} (hm : ((p ^ n : ℕ) : ℤ) • m = 0) :
    (c : ℤ) • m = ((c % p ^ n : ℕ) : ℤ) • m := by
  conv_lhs => rw [← Nat.div_add_mod c (p ^ n)]
  rw [Nat.cast_add, add_smul, Nat.cast_mul, mul_comm, mul_smul, hm, smul_zero, zero_add]

theorem natCast_smul_eq_of_zmod_eq {n c d : ℕ} {m : M} (hm : ((p ^ n : ℕ) : ℤ) • m = 0)
    (h : (c : ZMod (p ^ n)) = d) : (c : ℤ) • m = (d : ℤ) • m := by
  rw [natCast_smul_eq_mod hm, natCast_smul_eq_mod (c := d) hm, (ZMod.natCast_eq_natCast_iff' c d _).1 h]

variable [Fact p.Prime]

theorem toZModPow_eq_appr (n : ℕ) (a : ℤ_[p]) : PadicInt.toZModPow n a = (a.appr n : ZMod (p ^ n)) := rfl

theorem appr_succ_smul_eq (a : ℤ_[p]) (x : TateModule p M) (n : ℕ) :
    ((a.appr (n + 1) : ℕ) : ℤ) • (x : ℕ → M) n = ((a.appr n : ℕ) : ℤ) • (x : ℕ → M) n := by
  refine natCast_smul_eq_of_zmod_eq (torsion x n) ?_
  rw [← toZModPow_eq_appr, ← PadicInt.zmod_cast_comp_toZModPow n (n + 1) n.le_succ, RingHom.comp_apply,
    toZModPow_eq_appr, ZMod.castHom_apply, ZMod.cast_natCast (pow_dvd_pow p n.le_succ)]

end TateModule

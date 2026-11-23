module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite

public section


public theorem torsion (x : TateModule p M) (n : ℕ) : ((p ^ n : ℕ) : ℤ) • (x : ℕ → M) n = 0 := (x.2 n).1


public theorem compat (x : TateModule p M) (n : ℕ) : ((p : ℕ) : ℤ) • (x : ℕ → M) (n + 1) = (x : ℕ → M) n :=
  (x.2 n).2


@[simp] public theorem coe_add (x y : TateModule p M) : ((x + y : TateModule p M) : ℕ → M) = x + y := rfl

@[simp] public theorem coe_zero : ((0 : TateModule p M) : ℕ → M) = 0 := rfl

@[simp] public theorem coe_neg (x : TateModule p M) : ((-x : TateModule p M) : ℕ → M) = -x := rfl

@[simp] public theorem coe_sub (x y : TateModule p M) : ((x - y : TateModule p M) : ℕ → M) = x - y := rfl


public theorem natCast_smul_eq_mod {n c : ℕ} {m : M} (hm : ((p ^ n : ℕ) : ℤ) • m = 0) :
    (c : ℤ) • m = ((c % p ^ n : ℕ) : ℤ) • m := by
  conv_lhs => rw [← Nat.div_add_mod c (p ^ n)]
  rw [Nat.cast_add, add_smul, Nat.cast_mul, mul_comm, mul_smul, hm, smul_zero, zero_add]


public theorem natCast_smul_eq_of_zmod_eq {n c d : ℕ} {m : M} (hm : ((p ^ n : ℕ) : ℤ) • m = 0)
    (h : (c : ZMod (p ^ n)) = d) : (c : ℤ) • m = (d : ℤ) • m := by
  rw [natCast_smul_eq_mod hm, natCast_smul_eq_mod (c := d) hm, (ZMod.natCast_eq_natCast_iff' c d _).1 h]

variable [Fact p.Prime]


public theorem toZModPow_eq_appr (n : ℕ) (a : ℤ_[p]) : PadicInt.toZModPow n a = (a.appr n : ZMod (p ^ n)) := rfl


public theorem appr_succ_smul_eq (a : ℤ_[p]) (x : TateModule p M) (n : ℕ) :
    ((a.appr (n + 1) : ℕ) : ℤ) • (x : ℕ → M) n = ((a.appr n : ℕ) : ℤ) • (x : ℕ → M) n := by
  refine natCast_smul_eq_of_zmod_eq (torsion x n) ?_
  rw [← toZModPow_eq_appr, ← PadicInt.zmod_cast_comp_toZModPow n (n + 1) n.le_succ, RingHom.comp_apply,
    toZModPow_eq_appr, ZMod.castHom_apply, ZMod.cast_natCast (pow_dvd_pow p n.le_succ)]

end TateModule

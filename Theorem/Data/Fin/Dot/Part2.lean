import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Mul
import Def.Fun
import Instance.Data.Fin.Dot.Part2


theorem Dot.fun_out_eq [AddCommMonoid α] [Mul α] {m : ℕ} (s : Slice)
    (v : Fun (Fin m) α) (w : FunSlice.Out α s) :
    v @ w = Fin.dotResize v.toFun (w : Fin (s.stop.toNat - s.start.toNat) → α) := rfl

theorem Fin.resize_cast [Zero α] {m n : ℕ} (heq : m = n) (x : Fin m → α) (i : Fin n) :
    Fin.resize x n i = x (Fin.cast heq.symm i) := by
  unfold Fin.resize
  if hm : m = 0 then
    subst hm
    subst heq
    apply i.elim0
  else
    rw [dite_eq_right hm]
    have hn : n ≠ 0 := fun hz => hm (heq.trans hz)
    have hlt : (i : ℕ) < n / m * m := by
      rw [heq, Nat.div_self (Nat.pos_of_ne_zero hn), Nat.one_mul]
      apply i.isLt
    rw [dite_eq_left hlt]
    refine congrArg x (Fin.ext ?_)
    have hmod : (i : ℕ) % m = i := by
      rw [heq]
      apply Nat.mod_eq_of_lt i.isLt
    simp [hmod]

theorem Fin.dotResize_cast [AddCommMonoid α] [Mul α] {m n : ℕ} (h : n = m)
    (v : Fin m → α) (w : Fin n → α) :
    Fin.dotResize v w = ∑ i : Fin m, v i * w (Fin.cast h.symm i) := by
  unfold Fin.dotResize dotProduct
  rw [show m ⊔ n = m by rw [h]; apply Nat.max_self]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.resize_cast rfl, Fin.resize_cast h]
  simp

@[simp]
theorem Dot.fun_getSlice_eq [AddCommMonoid α] [Mul α]
    (v : Fun (Fin n) α) (f : Fun ℕ α) (k : ℕ) :
    v @ f[k: k + n] = ∑ i : Fin n, v.toFun i * f.toFun (k + i) := by
  have hto : ((k : ℤ) + (n : ℤ)).toNat = k + n := by
    rw [← Int.natCast_add]
    rfl
  have hlen : ((k : ℤ) + (n : ℤ)).toNat - (k : ℤ).toNat = n := by
    rw [hto, Int.toNat_natCast, Nat.add_sub_cancel_left]
  rw [Dot.fun_out_eq, Fin.dotResize_cast hlen]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Fun.getSlice, Function.getSlice, FunSlice.slice, Nat.add_comm]


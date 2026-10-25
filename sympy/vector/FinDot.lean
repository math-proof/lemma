import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Mul
import Def.Fun

class Dot (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  dot : α → β → γ

infixl:70 " @ " => Dot.dot

/-- Finite dot product: `v @ w = ∑ i, v i * w i`. -/
instance [Mul α] [AddCommMonoid α] [Fintype ι] : Dot (ι → α) (ι → α) α where
  dot := dotProduct

/-- `Fin n ⇀ α` on the left against a plain vector. -/
instance [Mul α] [AddCommMonoid α] [Fintype ι] : Dot (Fun ι α) (ι → α) α where
  dot v w := dotProduct v.toFun w

@[simp]
theorem Dot.fin_eq [Mul α] [AddCommMonoid α] [Fintype ι] (v w : ι → α) :
    v @ w = ∑ i, v i * w i := rfl

@[simp]
theorem Dot.fun_fin_eq [Mul α] [AddCommMonoid α] [Fintype ι] (v : Fun ι α) (w : ι → α) :
    v @ w = ∑ i, v.toFun i * w i := rfl

/-- Tile `x` up to `n' / n` copies and pad the rest with `0`, as in `List.Vector.resize`. -/
def Fin.resize [Zero α] {n : ℕ} (x : Fin n → α) (n' : ℕ) : Fin n' → α :=
  fun i =>
    if hn : n = 0 then
      0
    else if _h : (i : ℕ) < n' / n * n then
      x ⟨(i : ℕ) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
    else
      0

/-- Heterogeneous finite dot: resize both sides to `m ⊔ n`, then the ordinary dot product.
Same padding rule as `List.Vector`'s `@`. -/
def Fin.dotResize [AddCommMonoid α] [Mul α] {m n : ℕ} (v : Fin m → α) (w : Fin n → α) : α :=
  let k := m ⊔ n
  dotProduct (Fin.resize v k) (Fin.resize w k)

/-- `v @ w` when `w` is a closed slice `f[a:b]`, whose `Fin` length need not be definitionally
the length of `v`. -/
instance (priority := low) [AddCommMonoid α] [Mul α] {m : ℕ} (s : Slice) :
    Dot (Fun (Fin m) α) (FunSlice.Out α s) α where
  dot v w := Fin.dotResize v.toFun (w : Fin (s.stop.toNat - s.start.toNat) → α)

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

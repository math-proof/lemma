import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Mul
import Def.Fun
import Theorem.Data.Fin.Dot


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


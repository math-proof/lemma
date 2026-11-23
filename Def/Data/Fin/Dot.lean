module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Mul
public import Notation.Fun
public import Theorem.Data.Fin.Dot

@[expose] public section

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
Same padding rule as `List.Vector`'s `⬝ᵥ`. -/
def Fin.dotResize [AddCommMonoid α] [Mul α] {m n : ℕ} (v : Fin m → α) (w : Fin n → α) : α :=
  let k := m ⊔ n
  dotProduct (Fin.resize v k) (Fin.resize w k)


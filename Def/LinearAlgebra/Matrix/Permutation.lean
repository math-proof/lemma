import Def.Analysis.SpecialFunctions.TensorFunctions
import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Equiv.Defs


/-- py `SwapMatrix(n, i, j)`: the permutation matrix of the transposition `(i j)`.
Lean `Matrix` form (Fin indices; entries via `NatCast` from `KroneckerDelta`). -/
def swapMatrix {α : Type*} [NatCast α] {n : ℕ} (i j : Fin n) :
    Matrix (Fin n) (Fin n) α :=
  Matrix.of fun a b => KroneckerDelta (Equiv.swap i j a) b


/--
Row index map for an elementary row-shift:
if `i = j₀` then `i₀`;
else if `i ∈ Ioc j₀ i₀` then `i - 1`;
else if `i ∈ Ico i₀ j₀` then `i + 1`;
else `i`.
-/
def Fin.shiftRow {n : ℕ} (i i₀ j₀ : Fin n) : Fin n :=
  if i = j₀ then
    i₀
  else if h : i ∈ Set.Ioc j₀ i₀ then
    ⟨i - 1, by grind⟩
  else if h : i ∈ Set.Ico i₀ j₀ then
    ⟨i + 1, by grind⟩
  else
    i


/--
Elementary row-shift matrix:
delete row `i` and insert after row `j` when `i < j`;
delete row `i` and insert before row `j` when `j < i`.

`(P)_{a,b} = δ(a.shiftRow i₀ j₀, b)`.

\[
\det(\mathrm{shiftMatrix}(n,i,j))=(-1)^{j-i}
\]

(in ℤ; equivalently `(-1)^{|j-i|}`).

Lean `Matrix` form (Fin indices; entries via `NatCast` from `KroneckerDelta`).
-/
def shiftMatrix {α : Type*} [NatCast α] {n : ℕ} (i₀ j₀ : Fin n) :
    Matrix (Fin n) (Fin n) α :=
  Matrix.of fun a b => KroneckerDelta (a.shiftRow i₀ j₀) b


/--
Translation `x ↦ x + i` on `Fin n`.
-/
def Fin.addRight {n : ℕ} (i : Fin n) : Equiv (Fin n) (Fin n) where
  toFun x := x + i
  invFun y := ⟨((y : ℕ) + n - (i : ℕ)) % n, Nat.mod_lt _ (Fin.pos i)⟩
  left_inv x := by
    apply Fin.ext
    show (((x : ℕ) + (i : ℕ)) % n + n - (i : ℕ)) % n = (x : ℕ)
    have hx : (x : ℕ) < n := x.isLt
    have hi : (i : ℕ) < n := i.isLt
    have hmod1 : ∀ (a : ℕ), a < n → (a + n) % n = a := by
      intro a ha
      have key : (a + n) % n = a % n := by
        have e : a + n = a + n * 1 := by simp
        rw [e, Nat.add_mul_mod_self_left]
      exact key.trans (Nat.mod_eq_of_lt ha)
    by_cases h : (x : ℕ) + (i : ℕ) < n
    · rw [Nat.mod_eq_of_lt h]
      have h2 : (x : ℕ) + (i : ℕ) + n - (i : ℕ) = x + n := by omega
      rw [h2]
      exact hmod1 x hx
    · have h' : n ≤ (x : ℕ) + (i : ℕ) := by omega
      have hlt : (x : ℕ) + (i : ℕ) - n < n := by omega
      have hsub : (x : ℕ) + (i : ℕ) = n + ((x : ℕ) + (i : ℕ) - n) :=
        (Nat.add_sub_of_le h').symm
      have hm : ((x : ℕ) + (i : ℕ)) % n = (x : ℕ) + (i : ℕ) - n := by
        conv_lhs => rw [hsub, Nat.add_comm]
        exact hmod1 ((x : ℕ) + (i : ℕ) - n) hlt
      rw [hm]
      have h3 : (x : ℕ) + (i : ℕ) - n + n - (i : ℕ) = x := by omega
      rw [h3]
      exact Nat.mod_eq_of_lt hx
  right_inv y := by
    apply Fin.ext
    show (((y : ℕ) + n - (i : ℕ)) % n + (i : ℕ)) % n = (y : ℕ)
    have hy : (y : ℕ) < n := y.isLt
    have hi : (i : ℕ) < n := i.isLt
    have hmod1 : ∀ (a : ℕ), a < n → (a + n) % n = a := by
      intro a ha
      have key : (a + n) % n = a % n := by
        have e : a + n = a + n * 1 := by simp
        rw [e, Nat.add_mul_mod_self_left]
      exact key.trans (Nat.mod_eq_of_lt ha)
    rw [Nat.mod_add_mod]
    have h : (y : ℕ) + n - (i : ℕ) + (i : ℕ) = y + n := by omega
    rw [h]
    exact hmod1 y hy

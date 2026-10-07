import Mathlib.Tactic

/-! py `Stack[i](Piecewise(...))` with n blocks: the piecewise chain and its identification with the block concatenation.
-/

/-- py `Piecewise((X₀[i], i < n₀), (X₁[i - n₀], i < n₀ + n₁), …, (X_m[i - n₀ - … - n_{m-1}], True))`. -/
def Tensor.stackIte {α : Type*} : (m : ℕ) → (Fin (m + 1) → ℕ) → (Fin (m + 1) → ℕ → α) → ℕ → α
  | 0, _, f, i => f 0 i
  | m + 1, s, f, i => if i < s 0 then f 0 i else Tensor.stackIte m (Fin.tail s) (Fin.tail f) (i - s 0)



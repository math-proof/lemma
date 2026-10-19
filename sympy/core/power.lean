import Mathlib.Data.Finset.Basic

notation:max x "²" => x ^ 2  -- square
notation:max x "³" => x ^ 3  -- cube
notation:max x "⁴" => x ^ 4  -- tesseract

/-- `γ ^ f` for an exponent sequence `f : ℕ → ℕ`: the sequence `k ↦ γ ^ f k`; e.g. the discount
weights `γ ^ (id : ℕ → ℕ) = fun k ↦ γ ^ k` (sympy `γ ** Stack[k](k)`). -/
instance Function.instHPowNatSeq {α : Type u} [HPow α Nat α] : HPow α (Nat → Nat) (Nat → α) where
  hPow γ f := fun k ↦ γ ^ f k

@[simp]
theorem Function.hPow_apply {α : Type u} [HPow α Nat α] (γ : α) (f : Nat → Nat) (k : Nat) :
    (γ ^ f) k = γ ^ f k := rfl

/-- Finite-support geometric weights: `γ ^ s` for `s : Finset ℕ`. Used with `@` as
`∑ i ∈ s, γ^i * g i`. -/
structure FinsetPow (α : Type*) where
  base : α
  support : Finset ℕ

namespace FinsetPow

instance [HPow α ℕ α] : CoeFun (FinsetPow α) (fun _ => ℕ → α) where
  coe p := fun i => p.base ^ i

end FinsetPow

instance [HPow α ℕ α] : HPow α (Finset ℕ) (FinsetPow α) where
  hPow base support := ⟨base, support⟩

@[simp]
theorem FinsetPow.coe_apply [HPow α ℕ α] (γ : α) (s : Finset ℕ) (i : ℕ) :
    (γ ^ s : FinsetPow α) i = γ ^ i := rfl

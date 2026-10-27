import Mathlib.Data.Nat.GCD.Basic
import Def.Data.Holor.Defs.Part4
import Def.Data.List.Mul.Part2


namespace Tensor

theorem mul_shape_eq (s s' : List ℕ) :
    mul_shape s s' =
      (pad1 s (s.length ⊔ s'.length)).zipWith Nat.lcm
        (pad1 s' (s.length ⊔ s'.length)) :=
  rfl

theorem mul_shape_length (s s' : List ℕ) :
    (mul_shape s s').length = s.length ⊔ s'.length := by
  simp [mul_shape, List.length_zipWith, pad1_length_max, pad1_length_max']


theorem mul_shape_prod_eq_zero_iff (s s' : List ℕ) :
    (mul_shape s s').prod = 0 ↔ s.prod = 0 ∨ s'.prod = 0 := by
  rw [mul_shape_eq]
  simp [zipWith_lcm_prod_eq_zero_iff _ _ (pad1_length_eq s s'),
    pad1_prod]

end Tensor

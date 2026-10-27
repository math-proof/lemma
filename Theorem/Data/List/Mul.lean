import Mathlib.Data.Nat.GCD.Basic
import Def.Data.Holor.Defs.Part4
import Def.Data.List.Mul


namespace Tensor

theorem pad1_prod (s : List ℕ) (n : ℕ) :
    (pad1 s n).prod = s.prod := by
  simp [pad1, List.prod_replicate]

theorem pad1_length (s : List ℕ) (n : ℕ) (h : s.length ≤ n) :
    (pad1 s n).length = n := by
  simp [pad1]
  omega

theorem pad1_length_max (s s' : List ℕ) :
    (pad1 s (s.length ⊔ s'.length)).length = s.length ⊔ s'.length :=
  pad1_length s _ le_sup_left

theorem pad1_length_max' (s s' : List ℕ) :
    (pad1 s' (s.length ⊔ s'.length)).length = s.length ⊔ s'.length :=
  pad1_length s' _ le_sup_right

theorem pad1_length_eq (s s' : List ℕ) :
    (pad1 s (s.length ⊔ s'.length)).length =
      (pad1 s' (s.length ⊔ s'.length)).length := by
  rw [pad1_length_max, pad1_length_max']


theorem zipWith_lcm_prod_eq_zero_iff (s s' : List ℕ)
    (h : s.length = s'.length) :
    (s.zipWith Nat.lcm s').prod = 0 ↔ s.prod = 0 ∨ s'.prod = 0 := by
  induction s generalizing s' with
  | nil =>
    cases s' with
    | nil =>
      simp
    | cons _ _ =>
      cases h
  | cons n s ih =>
    cases s' with
    | nil =>
      cases h
    | cons n' s' =>
      simp only [List.zipWith, List.prod_cons, Nat.mul_eq_zero, Nat.lcm_eq_zero_iff]
      rw [ih s' (Nat.succ_injective h)]
      tauto


end Tensor

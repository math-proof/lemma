/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/HsuShiueGeneralizedStirlingNumber.lean -/


import sympy.atlas.Combinatorics.Enumerative.HsuShiueGeneralizedStirlingNumber
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Tactic

namespace MetaMathlibExt

variable {K : Type*} [RCLike K]

example (z alpha : K) : generalizedFallingFactorial z alpha 0 = 1 := rfl

example (z alpha : K) : generalizedFallingFactorial z alpha 2 = z * (z - alpha) := by
  simp [generalizedFallingFactorial]

example (S : ℕ → ℕ → K) (alpha beta r : K)
    (hS : IsHsuShiueFamily S alpha beta r) {n k : ℕ} (hnk : n < k) :
    S n k = 0 :=
  hS.2.2.1 n k hnk

/-- At `(alpha, beta, r) = (0, 1, 0)`, the family is the classical Stirling
numbers of the second kind. -/
example : IsHsuShiueFamily
    (fun n k ↦ (Nat.stirlingSecond n k : ℝ)) 0 1 0 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · intro n
    cases n <;> simp [generalizedFallingFactorial]
  · intro n k hnk
    simp [Nat.stirlingSecond_eq_zero_of_lt hnk]
  · intro n k
    simp [Nat.stirlingSecond_succ_succ]
    ring

end MetaMathlibExt

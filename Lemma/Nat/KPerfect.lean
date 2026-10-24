import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.KPerfect
open Nat


namespace Nat

/--
[IsKPerfect.pos_k](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KPerfect.lean)
-/
@[path]
lemma IsKPerfect.pos_k
  {k n : ℕ}
-- given
  (h : IsKPerfect k n) :
-- imply
  0 < k := by
-- proof
  have hsigma : 0 < (ArithmeticFunction.sigma 1) n :=
    ArithmeticFunction.sigma_pos 1 n h.1.ne'
  rw [h.2] at hsigma
  exact Nat.pos_of_mul_pos_right hsigma

end Nat

namespace Nat

/--
[isKPerfect_two_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KPerfect.lean)
-/
@[path]
lemma isKPerfect_two_iff
  {n : ℕ} :
-- imply
  IsKPerfect 2 n ↔ n.Perfect := by
-- proof
  constructor
  · rintro ⟨hn, hsigma⟩
    rw [ArithmeticFunction.sigma_one_apply] at hsigma
    exact (perfect_iff_sum_divisors_eq_two_mul hn).2 hsigma
  · intro hn
    refine ⟨hn.2, ?_⟩
    rw [ArithmeticFunction.sigma_one_apply]
    exact (perfect_iff_sum_divisors_eq_two_mul hn.2).1 hn

end Nat


-- created on 2026-10-20
-- updated on 2026-10-23

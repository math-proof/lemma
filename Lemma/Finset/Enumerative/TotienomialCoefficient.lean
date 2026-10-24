import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.TotienomialCoefficient
open MetaMathlibExt


namespace MetaMathlibExt

/--
[generalizedFactorial_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/TotienomialCoefficient.lean)
-/
@[path]
lemma generalizedFactorial_pos
  {f : ℕ → ℕ}
  {n : ℕ}
-- given
  (hf : IsPositiveSequence f) :
-- imply
  0 < generalizedFactorial f n := by
-- proof
  apply Finset.prod_pos
  intro i hi
  exact hf i (Finset.mem_Icc.mp hi).1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[generalizedBinomialCoefficient_mul_denominator](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/TotienomialCoefficient.lean)
-/
@[path]
lemma generalizedBinomialCoefficient_mul_denominator
  {f : ℕ → ℕ}
  {n m : ℕ}
-- given
  (hf : IsPositiveSequence f) :
-- imply
  generalizedBinomialCoefficient f n m *
        ((generalizedFactorial f n : ℚ) * (generalizedFactorial f m : ℚ)) =
      generalizedFactorial f (n + m) := by
-- proof
  apply div_mul_cancel₀
  exact mul_ne_zero
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (generalizedFactorial_pos hf n)))
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (generalizedFactorial_pos hf m)))

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23

import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.TotienomialCoefficient
open MetaMathlibExt


/--
[generalizedFactorial_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/TotienomialCoefficient.lean)
-/
@[path]
private lemma generalizedFactorial_pos_eq
  {f : ℕ → ℕ}
  {n : ℕ}
-- given
  (hf : IsPositiveSequence f) :
-- imply
  0 < generalizedFactorial f n := by
-- proof
  apply MetaMathlibExt.generalizedFactorial_pos hf n

/--
[generalizedBinomialCoefficient_mul_denominator](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/TotienomialCoefficient.lean)
-/
@[path]
private lemma generalizedBinomialCoefficient_mul_denominator_eq
  {f : ℕ → ℕ}
  {n m : ℕ}
-- given
  (hf : IsPositiveSequence f) :
-- imply
  generalizedBinomialCoefficient f n m *
        ((generalizedFactorial f n : ℚ) * (generalizedFactorial f m : ℚ)) =
      generalizedFactorial f (n + m) := by
-- proof
  apply MetaMathlibExt.generalizedBinomialCoefficient_mul_denominator hf n m


-- created on 2026-10-20

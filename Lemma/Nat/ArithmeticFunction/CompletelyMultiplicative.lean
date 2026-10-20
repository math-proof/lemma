import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ArithmeticFunction.CompletelyMultiplicative
open ArithmeticFunction


/--
[IsCompletelyMultiplicative.map_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/CompletelyMultiplicative.lean)
-/
@[path]
private lemma IsCompletelyMultiplicative_map_mul_eq
  [Mul R] [Zero R]
  {f : ArithmeticFunction R}
  {m n : ℕ}
-- given
  (hf : f.IsCompletelyMultiplicative) :
-- imply
  f (m * n) = f m * f n := by
-- proof
  apply ArithmeticFunction.IsCompletelyMultiplicative.map_mul hf m n

/--
[IsCompletelyMultiplicative.isMultiplicative](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/CompletelyMultiplicative.lean)
-/
@[path]
private lemma IsCompletelyMultiplicative_isMultiplicative_eq
  [MonoidWithZero R]
  {f : ArithmeticFunction R}
-- given
  (hf : f.IsCompletelyMultiplicative)
  (h0 : f 1 = 1) :
-- imply
  f.IsMultiplicative := by
-- proof
  apply ArithmeticFunction.IsCompletelyMultiplicative.isMultiplicative hf h0


-- created on 2026-10-20

import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ArithmeticFunction.CompletelyMultiplicative
open ArithmeticFunction


namespace ArithmeticFunction

/--
[IsCompletelyMultiplicative.map_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/CompletelyMultiplicative.lean)
-/
@[path]
lemma IsCompletelyMultiplicative.map_mul
  [Mul R] [Zero R]
  {f : ArithmeticFunction R}
  {m n : ℕ}
-- given
  (hf : f.IsCompletelyMultiplicative) :
-- imply
  f (m * n) = f m * f n :=
-- proof
  hf m n

end ArithmeticFunction

namespace ArithmeticFunction

/--
[IsCompletelyMultiplicative.isMultiplicative](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/CompletelyMultiplicative.lean)
-/
@[path]
lemma IsCompletelyMultiplicative.isMultiplicative
  [MonoidWithZero R]
  {f : ArithmeticFunction R}
-- given
  (hf : f.IsCompletelyMultiplicative)
  (h0 : f 1 = 1) :
-- imply
  f.IsMultiplicative :=
-- proof
  ⟨h1, fun _ => hf _ _⟩

end ArithmeticFunction


-- created on 2026-10-20
-- updated on 2026-10-23

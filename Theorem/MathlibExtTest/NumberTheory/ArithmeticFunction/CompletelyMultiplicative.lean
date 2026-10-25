/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ArithmeticFunction/CompletelyMultiplicative.lean -/

/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/


import Def.NumberTheory.ArithmeticFunction.CompletelyMultiplicative
import Lemma.Nat.ArithmeticFunction.CompletelyMultiplicative
/-!
# Tests for completely multiplicative arithmetic functions

Checks `IsCompletelyMultiplicative.map_mul`, the normalization bridge
`IsCompletelyMultiplicative.isMultiplicative`, and the zero-function
boundary: `0` is completely multiplicative but not `IsMultiplicative`.
-/


namespace ArithmeticFunctionTest

-- Elimination theorem: `map_mul` extracts the defining equation.
example {R : Type*} [Mul R] [Zero R] (f : ArithmeticFunction R)
    (hf : f.IsCompletelyMultiplicative) (m n : ℕ) :
    f (m * n) = f m * f n :=
  hf.map_mul m n

-- Normalization bridge: completely multiplicative + `f 1 = 1` gives
-- Mathlib's `IsMultiplicative`.
example {R : Type*} [MonoidWithZero R] (f : ArithmeticFunction R)
    (hf : f.IsCompletelyMultiplicative) (h1 : f 1 = 1) :
    f.IsMultiplicative :=
  hf.isMultiplicative h1

-- The zero arithmetic function is completely multiplicative.
example {R : Type*} [MulZeroClass R] :
    (0 : ArithmeticFunction R).IsCompletelyMultiplicative := by
  intro m n
  simp

-- The zero function does not imply normalized multiplicativity:
-- `IsMultiplicative` requires `f 1 = 1`, which `0` fails.
example : ¬ (0 : ArithmeticFunction ℕ).IsMultiplicative := by
  intro h
  have h1 := h.1
  simp at h1

end ArithmeticFunctionTest

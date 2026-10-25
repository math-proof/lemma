/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/CompletelyMultiplicative.lean -/

/-
Copyright (c) 2026 Alex Kontorovich and contributors, Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich and contributors, Adam Kiezun
-/

import Mathlib.NumberTheory.ArithmeticFunction.Defs
/-!
# Completely multiplicative arithmetic functions

This module defines `ArithmeticFunction.IsCompletelyMultiplicative`,
its projection `IsCompletelyMultiplicative.map_mul`, and the
normalization bridge `IsCompletelyMultiplicative.isMultiplicative` to
`ArithmeticFunction.IsMultiplicative`.

References: arXiv:2304.03121v4 `main.tex` lines 237--241
(Furstenberg systems of pretentious and MRT multiplicative functions);
PrimeNumberTheoremAnd at revision `be5e07e04cde20c5ceabf63759bd097a9c88173f`.
-/


namespace ArithmeticFunction

variable {R : Type*}

/-- `f` is completely multiplicative if `f (m * n) = f m * f n` for all `m, n : ℕ`. -/
def IsCompletelyMultiplicative [Mul R] [Zero R] (f : ArithmeticFunction R) : Prop :=
  ∀ m n : ℕ, f (m * n) = f m * f n

end ArithmeticFunction

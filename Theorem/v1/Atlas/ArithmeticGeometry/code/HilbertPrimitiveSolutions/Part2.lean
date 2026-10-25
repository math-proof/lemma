/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertSymbol
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertFormulaOdd
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Hilbert2Adic
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Hilbert2AdicCore
import Def.v1.Atlas.ArithmeticGeometry.code.HilbertFormulaOdd
import Def.v1.Atlas.ArithmeticGeometry.code.Hilbert2Adic
import Def.v1.Atlas.ArithmeticGeometry.code.Hilbert2AdicCore.Part2
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Instance.v1.Atlas.ArithmeticGeometry.code.HilbertPrimitiveSolutions.Part3
open scoped Classical


section PadicBilinearHelpers

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

open HilbertSymbol

namespace hilbertSymbol

variable {F : Type*} [Field F]

/-- Wrapper exposing `HilbertBilinearField.isSolvable_mul_of_both_neg` in the
`hilbertSymbol` namespace. -/
theorem isSolvable_mul_of_both_neg [HilbertBilinearField F]
    (a b c : Fˣ)
    (ha : hilbertSymbol F a c = -1) (hb : hilbertSymbol F b c = -1) :
    hilbertSymbol F (a * b) c = 1 :=
  HilbertBilinearField.isSolvable_mul_of_both_neg a b c ha hb

/-- Nondegeneracy axiom of `HilbertBilinearField`, exposed in the `hilbertSymbol` namespace:
every non-square unit pairs to $-1$ with some element. -/
theorem nondegenerate [HilbertBilinearField F] (c : Fˣ) (hc : ¬ IsSquare (c : F)) :
    ∃ b : Fˣ, hilbertSymbol F b c = -1 :=
  HilbertBilinearField.nondegenerate c hc

end hilbertSymbol
end PadicBilinearHelpers

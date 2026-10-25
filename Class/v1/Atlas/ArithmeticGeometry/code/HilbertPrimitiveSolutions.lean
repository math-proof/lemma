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
open scoped Classical


/-- A characteristic-zero field on which the Hilbert symbol is bilinear and nondegenerate.
The two structural axioms encode: (i) if both $(a,c)_F$ and $(b,c)_F$ equal $-1$ then
$(ab,c)_F = 1$ (used to derive bilinearity); (ii) for every non-square unit $c$ there
exists $b$ with $(b,c)_F = -1$ (nondegeneracy of the Hilbert pairing). -/
class HilbertBilinearField (F : Type*) [Field F] extends CharZero F where
  isSolvable_mul_of_both_neg : ∀ (a b c : Fˣ),
    hilbertSymbol F a c = -1 → hilbertSymbol F b c = -1 →
    hilbertSymbol F (a * b) c = 1
  nondegenerate : ∀ (c : Fˣ), ¬ IsSquare (c : F) →
    ∃ b : Fˣ, hilbertSymbol F b c = -1


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
import Instance.v1.Atlas.ArithmeticGeometry.code.HilbertPrimitiveSolutions
open scoped Classical


section PadicBilinearHelpers

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

open HilbertSymbol

/-- Decidable witness predicate for $2$-adic nondegeneracy: a unit $w_0 \in (\mathbb{Z}/8)^\times$
has either a unit $v_0$ with $z^2 = v_0 x^2 + w_0 y^2$ insolvable mod $8$, or a unit $v_0$
with $z^2 = 2v_0 x^2 + w_0 y^2$ insolvable mod $8$. -/
@[reducible] def nondeg_unit_combined (w₀ : (ZMod (2 ^ 3))ˣ) : Prop :=
  (∃ (v₀ : (ZMod (2 ^ 3))ˣ), ¬ hasPrimSolMod8_one_loc v₀ w₀) ∨
  (∃ (v₀ : (ZMod (2 ^ 3))ˣ), ¬ hasPrimSolMod8_two_loc v₀ w₀)

end PadicBilinearHelpers

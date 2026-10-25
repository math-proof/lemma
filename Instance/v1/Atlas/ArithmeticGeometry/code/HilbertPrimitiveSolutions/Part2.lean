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
import Def.v1.Atlas.ArithmeticGeometry.code.HilbertPrimitiveSolutions
open scoped Classical


section PadicBilinearHelpers

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

open HilbertSymbol

/-- Decidability of `nondeg_unit_combined` from decidability of each disjunct. -/
instance (w₀ : (ZMod (2 ^ 3))ˣ) : Decidable (nondeg_unit_combined w₀) :=
  instDecidableOr

/-- Decidability of `nondeg_two_prop` via finite search over $(\mathbb{Z}/8)^\times$. -/
instance (w₀ : (ZMod (2 ^ 3))ˣ) : Decidable (nondeg_two_prop w₀) :=
  Fintype.decidableExistsFintype

end PadicBilinearHelpers

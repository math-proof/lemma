module
public import Def.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol.Part2
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertSymbol
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertFormulaOdd
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.Hilbert2Adic
public import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Hilbert2AdicCore
public import Def.v1.Atlas.ArithmeticGeometry.code.HilbertFormulaOdd
public import Def.v1.Atlas.ArithmeticGeometry.code.Hilbert2Adic
public import Def.v1.Atlas.ArithmeticGeometry.code.Hilbert2AdicCore.Part2
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Instance.v1.Atlas.ArithmeticGeometry.code.HilbertPrimitiveSolutions.Part2
open scoped Classical


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
section PadicBilinearHelpers

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

open HilbertSymbol

/-- Reduction modulo $8$ of a $2$-adic unit, producing a unit of $\mathbb{Z}/8$. -/
noncomputable def toZMod8Unit (w : ℤ_[2]ˣ) : (ZMod (2 ^ 3))ˣ :=
  ((PadicInt.isUnit_toZModPow_iff (show 0 < 3 from by omega)).mpr w.isUnit).unit

end PadicBilinearHelpers

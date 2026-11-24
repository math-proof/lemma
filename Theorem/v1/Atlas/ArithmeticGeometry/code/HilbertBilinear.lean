module
public import Def.v1.Atlas.ArithmeticGeometry.code.HilbertFormulaOdd
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertFormulaOdd
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertSymbol2Adic
public import Def.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol2Adic


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertBilinear.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped Classical

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

end

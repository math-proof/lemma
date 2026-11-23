/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EllipticFunction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.EllipticCurves.code.Lattice.Part2
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.Lattice
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.ComplexAnalysis
public import Def.v1.Atlas.EllipticCurves.code.ComplexAnalysis.Part3
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Meromorphic.Order
public import Def.v1.Atlas.EllipticCurves.code.EllipticFunction
open Complex


public noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

/-- Definition 14.8: an elliptic function for `L` is a meromorphic function on `ℂ`
that is `L`-periodic. -/
structure IsEllipticFunction (f : ℂ → ℂ) : Prop where
  meromorphic : Meromorphic f
  periodic : L.IsLatticePeriodic f

end ComplexLattice
end

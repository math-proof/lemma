/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EllipticFunction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.Lattice.Part2
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Lattice
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ComplexAnalysis
import Def.v1.Atlas.EllipticCurves.code.ComplexAnalysis.Part3
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Def.v1.Atlas.EllipticCurves.code.EllipticFunction
open Complex


noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

/-- Definition 14.8: an elliptic function for `L` is a meromorphic function on `ℂ`
that is `L`-periodic. -/
structure IsEllipticFunction (f : ℂ → ℂ) : Prop where
  meromorphic : Meromorphic f
  periodic : L.IsLatticePeriodic f

end ComplexLattice
end

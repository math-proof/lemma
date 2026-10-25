/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexTorus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.Lattice.Part2
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Lattice
import Theorem.v1.Atlas.EllipticCurves.code.ComplexTorus
open Complex ComplexLattice


noncomputable section

namespace ComplexTorus

variable (L : ComplexLattice)

/-- The canonical projection `ℂ →+ ℂ / L` sending a complex number to its class
in the complex torus, as an additive group homomorphism. -/
def proj : ℂ →+ ComplexTorus L :=
  QuotientAddGroup.mk' L.toAddSubgroup

end ComplexTorus
end

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.EllipticFunction.Part3
import Lemma.Complex.Atlas.v1.EllipticCurves.code.EllipticFunction
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Theorem161
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Uniformization
import Structure.v1.Atlas.EllipticCurves.code.Theorem161
import Def.v1.Atlas.EllipticCurves.code.Uniformization
import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication


namespace ComplexLattice

noncomputable section

open Pointwise

/-- Characterization of membership in the endomorphism ring: $\alpha \in \mathrm{End}(L)$
iff $\alpha \cdot z \in L$ for every $z \in L$. -/
@[simp]
theorem mem_endomorphismRing {L : ComplexLattice} {α : ℂ} :
    α ∈ L.endomorphismRing ↔ ∀ z ∈ L.toAddSubgroup, α * z ∈ L.toAddSubgroup :=
  Iff.rfl

end
end ComplexLattice

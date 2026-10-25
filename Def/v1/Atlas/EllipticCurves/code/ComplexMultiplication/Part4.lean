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
import Theorem.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part3


namespace ComplexLattice

noncomputable section

open Pointwise

/-- For an order $\mathcal{O}$ in an imaginary quadratic field, the ideal class group
is in canonical bijection with the set of homothety classes of proper $\mathcal{O}$-ideals. -/
def idealClassGroup_equiv_homothetyClass (𝒪 : Subring ℂ) (h𝒪 : IsImagQuadOrder 𝒪) :
    IdealClassGroup 𝒪 ≃ HomothetyClassCM 𝒪 :=
  Quotient.congr (Equiv.refl _)
    (fun L₁ L₂ => isEquivalent_iff_isHomothetic_properIdeal 𝒪 h𝒪 L₁ L₂)

end
end ComplexLattice

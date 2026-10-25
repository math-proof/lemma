/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMDefinition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part6
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ComplexMultiplication


namespace ComplexMultiplication

open ComplexLattice

noncomputable section

/-- A complex lattice $L$ has *complex multiplication* if its endomorphism ring
contains an element that is not an integer.  Equivalently (Definition 12.21),
$\mathrm{End}(L) \not\cong \mathbb{Z}$. -/
def HasCM (L : ComplexLattice) : Prop :=
  ∃ α : ℂ, α ∈ L.endomorphismRing ∧ ∀ n : ℤ, α ≠ (n : ℂ)

/-- The lattice $L$ has complex multiplication *by the order* $\mathcal{O}$
if $L$ is a proper $\mathcal{O}$-ideal and $\mathcal{O}$ is an order in an
imaginary quadratic field. -/
def HasCMBy (L : ComplexLattice) (𝒪 : Subring ℂ) : Prop :=
  ComplexLattice.IsProperIdeal 𝒪 L ∧ ComplexLattice.IsImagQuadOrder 𝒪

end
end ComplexMultiplication

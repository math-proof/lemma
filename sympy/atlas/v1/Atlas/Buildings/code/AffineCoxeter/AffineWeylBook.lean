/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.SemidirectProduct
import sympy.atlas.v1.Atlas.Buildings.code.Reflection.AffineWeylSemidirectMulEquiv
import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.TransitiveAlcovesHelper

open scoped InnerProductSpace
open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineReflectionGroup

variable (W : AffineReflectionGroup E)

/-- The "normal direction" of an affine hyperplane: the 1-dimensional submodule
spanned by its normal vector. Two parallel hyperplanes share the same normal
direction. -/
def normalDirection (η : AffineHyperplane E) : Submodule ℝ E :=
  Submodule.span ℝ {η.normal}

/-- An affine reflection group is `NegIdFree` if the linear-part group does not
contain the negation $-\mathrm{id}_E$. This rules out the "$\bar W = \{\pm 1\}$"
degeneracy that would obstruct faithfulness of $\bar W$ on normal directions. -/
class NegIdFree (W : AffineReflectionGroup E) : Prop where
  neg_id_not_mem : ∀ (wbar : E ≃ₗᵢ[ℝ] E), wbar ∈ W.LinearPartGroup →
    (∀ v : E, wbar v = -v) → False

end AffineReflectionGroup

namespace AffineWeylGroup

/-- Package an affine Weyl group $Wa$ (together with compatible full-data
$dFull$) as an `AffineWeylSemidirectData`, providing the data needed to express
the semi-direct product $W_a = \Lambda(\Phi^\vee) \rtimes W$. -/
def semidirect_product_decomposition_group
    (d : AffineWeylSemidirectData E) :
    ↥d.affineWeylSubgroup ≃* d.SemiType :=
  d.affineWeyl_semidirect_equiv

end AffineWeylGroup

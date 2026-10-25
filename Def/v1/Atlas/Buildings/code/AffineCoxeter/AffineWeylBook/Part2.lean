/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.AffineCoxeter.SemidirectProduct
import Def.v1.Atlas.Buildings.code.Reflection.AffineWeylSemidirectMulEquiv.Part3
import Theorem.v1.Atlas.Buildings.code.AffineCoxeter.TransitiveAlcovesHelper
import Class.v1.Atlas.Buildings.code.AffineCoxeter.AffineWeylBook
open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineWeylGroup

/-- Package an affine Weyl group $Wa$ (together with compatible full-data
$dFull$) as an `AffineWeylSemidirectData`, providing the data needed to express
the semi-direct product $W_a = \Lambda(\Phi^\vee) \rtimes W$. -/
def semidirect_product_decomposition_group
    (d : AffineWeylSemidirectData E) :
    ↥d.affineWeylSubgroup ≃* d.SemiType :=
  d.affineWeyl_semidirect_equiv

end AffineWeylGroup
end

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalCFT.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.NumberTheoryI.code.LocalCFT.Part2
open scoped RestrictedProduct
open Filter Set


noncomputable section

open scoped Pointwise

attribute [instance] LocalArtinReciprocity.kx_comm_group
  LocalArtinReciprocity.kx_topological_space
  LocalArtinReciprocity.kx_topological_group
  LocalArtinReciprocity.ext_preorder
  LocalArtinReciprocity.gal_comm_group
  LocalArtinReciprocity.gal_fintype

namespace LocalArtinReciprocity

variable (D : LocalArtinReciprocity)

class LocalExistenceTheorem (D : LocalArtinReciprocity) : Prop where
  open_finiteIndex_isNormGroup :
    ∀ (H : Subgroup D.Kx), H.FiniteIndex → IsOpen (H : Set D.Kx) → D.IsNormGroup H

end LocalArtinReciprocity
end

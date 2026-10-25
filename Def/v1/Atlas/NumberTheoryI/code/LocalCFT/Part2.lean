/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalCFT.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.NumberTheoryI.code.LocalCFT
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

def IsNormGroup (H : Subgroup D.Kx) : Prop :=
  ∃ i : D.I, D.normGroup i = H


def normSubgroup (i : D.I) : Subgroup D.Kx := D.normGroup i

def artinMap_quotient_equiv (i : D.I) :
    D.Kx ⧸ (D.normGroup i) ≃* D.GalLK i := by
  rw [← D.artinMap_ker i]
  exact QuotientGroup.quotientKerEquivOfSurjective _ (D.artinMap_surjective i)

end LocalArtinReciprocity
end

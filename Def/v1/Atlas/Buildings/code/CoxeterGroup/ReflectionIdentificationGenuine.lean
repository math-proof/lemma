/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ReflectionIdentificationGenuine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.CoxeterGroup.StrongExchangeProof
import Structure.v1.Atlas.Buildings.code.CoxeterGroup.ReflectionIdentificationGenuine
set_option linter.unusedSectionVars false


namespace CoxeterReflectionId

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- Converse bridge: an existing reflection-identification hypothesis yields the
inversion-difference bridge hypothesis. -/
def bridge_from_reflection_id {W : Type*} [Group W]
    {M : CoxeterMatrix B} {cs : CoxeterSystem M W}
    (hid : CoxeterBruhat.ReflectionIdentificationHyp cs) :
    InversionDifferenceBridgeHyp cs where
  identify_from_inversions := hid.identify

end CoxeterReflectionId

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnFlagToFrame.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnSimultaneousRefinement
import Structure.v1.Atlas.Buildings.code.SphericalBuilding.GLnFlagToFrame


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- Package the extracted lines into a `Frame k n`, witnessing the flag-to-frame hypothesis. -/
noncomputable def flagToFrameOfBasis
    (hyp : BasisFromFlagHyp k n) : FlagToFrameHyp k n where
  flag_to_frame := fun chain hchain hlen hproper => by

    obtain ⟨lines, h_dim, h_indep, h_span, h_compat⟩ :=
      hyp.extract chain hchain hlen hproper

    let F : Frame k n :=
      { lines := lines
        one_dim := h_dim
        indep := h_indep
        spanning := h_span }


    exact ⟨F, fun V hV => h_compat V hV⟩

end GLnBuilding

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnCommonApartment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnInstance


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- Hypothesis: any finite list of proper non-zero subspaces is simultaneously compatible
with some frame $F$ — i.e.\ admits a common adapted basis. -/
structure SimultaneousRefinementHyp where
  refine_list : ∀ (subs : List (Submodule k (Vec k n))),
    (∀ V ∈ subs, V ≠ ⊥ ∧ V ≠ ⊤) →
    ∃ F : Frame k n, ∀ V ∈ subs, F.IsCompatible k n V

end GLnBuilding

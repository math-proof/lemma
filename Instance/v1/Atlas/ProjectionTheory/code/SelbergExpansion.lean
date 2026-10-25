/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProjectionTheory.code.SelbergExpansion
open Matrix Finset BigOperators


noncomputable section

namespace SelbergExpansion

section GeneralGroup

variable {G : Type*} [Fintype G] [DecidableEq G] [Group G]

/-- Decidable equality on `SL₂(𝔽_p)` inherited from the underlying matrix subtype. -/
instance : DecidableEq (SL2 p) := Subtype.instDecidableEq

end GeneralGroup
end SelbergExpansion
end

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MacLaneCoherence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.CategoryTheory.Monoidal.Free.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category


namespace EGNO.MacLaneCoherence

section FreeMonoidalCoherence

/-- The full normalization isomorphism in the free monoidal category, witnessing that
every object is canonically isomorphic to its normalized form. -/
def macLane_coherence_normalization (C : Type*) :
    𝟭 (FreeMonoidalCategory C) ≅
      FreeMonoidalCategory.fullNormalize C ⋙ FreeMonoidalCategory.inclusion :=
  FreeMonoidalCategory.fullNormalizeIso C

end FreeMonoidalCoherence
end EGNO.MacLaneCoherence

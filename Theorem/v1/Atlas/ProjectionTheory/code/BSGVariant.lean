/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BSGVariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProjectionTheory.code.KeyLemmaBSG
import Lemma.Real.Atlas.v1.ProjectionTheory.code.KeyLemmaBSG
import Lemma.Real.Atlas.v1.ProjectionTheory.code.BSGProposition
import Def.v1.Atlas.ProjectionTheory.code.BSGProposition
/--
Balog–Szemerédi–Gowers (projection variant). For a commutative ring `G` and any
parameter `t ∈ G`, define the projection `πₜ(a, b) = a + t·b`. If
`X ⊆ A × B` with `|A|, |B| ≤ N`, `|X| ≥ K⁻¹ N²` and `|πₜ(X)| ≤ K N`, then there
exist refined subsets `A' ⊆ A`, `B' ⊆ B` such that `|X ∩ (A' × B')| ≳ K^{-O(1)} N²`
and `|πₜ(A' × B')| ≲ K^{O(1)} N`. This is the form of BSG used in the proof of
the Bourgain–Katz–Tao sum-product theorem.
-/


namespace ProjectionTheory

open Finset

end ProjectionTheory

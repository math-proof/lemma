/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers.Part4
import Theorem.v1.Atlas.Buildings.code.Reflection.WallSeparationCorollary
import Def.v1.Atlas.Buildings.code.Reflection.AffineWeylGroups.Part3
set_option maxHeartbeats 800000

open scoped InnerProductSpace
open Set

set_option maxHeartbeats 800000


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An affine Weyl group on $E$: a packaging of root-system data with a compatible affine
reflection group whose arrangement is the affine arrangement $\{H_{α,k}\}$ and whose
linear part equals the linear Weyl group. -/
structure AffineWeylGroup (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  data : AffineWeylGroupData E
  reflGroup : AffineReflectionGroup E
  arrangement_eq : reflGroup.arrangement = data.affineArrangement
  linearPart_eq : reflGroup.LinearPartGroup = data.weylGroup

end

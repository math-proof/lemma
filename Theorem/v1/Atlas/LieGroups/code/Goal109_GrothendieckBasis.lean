module
public import Def.v1.Atlas.LieGroups.code.GrothendieckGroupO.Part4
public import Theorem.Finset.Zero.le.Form.of.In_PosRoots
set_option maxHeartbeats 400000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/Goal109_GrothendieckBasis.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped TensorProduct
open ProjectiveFunctors Classical

universe u

variable {R : Type u} [CommRing R]
variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

end

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.TensorCategories.code.GrothendieckRing

@[expose] public section
set_option maxHeartbeats 800000

open Finset


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- The basis vector indexed by i ∈ ι, given by the indicator function of {i}. -/
def basisVec (i : ι) : GrRing ι :=
  fun k => if k = i then 1 else 0

end FusionRing

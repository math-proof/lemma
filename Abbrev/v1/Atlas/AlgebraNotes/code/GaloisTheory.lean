/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/GaloisTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraNotes.code.GaloisTheory


namespace GaloisTheory

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

set_option maxHeartbeats 400000 in

abbrev IsSolvableGroup (G : Type*) [Group G] : Prop := IsSolvable G

end GaloisTheory

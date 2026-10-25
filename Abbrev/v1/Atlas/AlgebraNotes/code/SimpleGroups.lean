/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/SimpleGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.AlgebraNotes.code.SimpleGroups


namespace SimpleGroups

open Matrix

section OneParamSubgroupTheorem

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

end OneParamSubgroupTheorem
end SimpleGroups

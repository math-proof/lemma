/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6overlapsplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc3_minimalwitnessencoded
import Inductive.StatisticalMechanics.Code.Walls.rc6overlapsplit
open Finset


namespace StatMech.Walls

open StatMech ConfigSpace


namespace WitnessClass

instance : Inhabited WitnessClass := ⟨neither⟩

end WitnessClass
end StatMech.Walls

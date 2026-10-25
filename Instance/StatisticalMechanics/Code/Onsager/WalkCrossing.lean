/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.BaseCase
import Theorem.StatisticalMechanics.Code.Onsager.NoDoubleWind
import Def.StatisticalMechanics.Code.Onsager.WalkCrossing


namespace StatMech.Onsager.WalkCrossing

open Finset

open StatMech.Onsager.BaseCase

open StatMech.Onsager.NoDoubleWind

variable {n : ℕ} [NeZero n]


instance decVert (w : Fin 4) : Decidable (isVertEdge w) := by unfold isVertEdge; infer_instance

instance decHoriz (w : Fin 4) : Decidable (isHorizEdge w) := by unfold isHorizEdge; infer_instance


end StatMech.Onsager.WalkCrossing

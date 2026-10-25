/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc76halladaptive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part7
import Theorem.StatisticalMechanics.Code.Walls.rc78hallmarriage.Part6
import Def.StatisticalMechanics.Code.Walls.rc76halladaptive.Part4
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


instance (A B : Finset (ConfigSpace (Fin 2))) : Decidable (rc76_marriage A B) := by
  unfold rc76_marriage; infer_instance


end StatMech.Walls

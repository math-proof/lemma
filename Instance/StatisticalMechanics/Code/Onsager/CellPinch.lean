/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellPinch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellEuler.Part3
import Def.StatisticalMechanics.Code.Onsager.CellPinch


namespace StatMech.Onsager.CellPinch

open Finset StatMech.Onsager.CellCount StatMech.Onsager.CellEuler


instance (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) : Decidable (pinchAt S v) := by
  unfold pinchAt; infer_instance


end StatMech.Onsager.CellPinch

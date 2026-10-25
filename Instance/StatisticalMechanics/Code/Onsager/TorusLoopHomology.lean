/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.DecorationSum.Part4
import Theorem.StatisticalMechanics.Code.Onsager.TorusLoopCharacter.Part2
import Def.StatisticalMechanics.Code.Onsager.TorusLoopHomology


namespace StatMech.Onsager

open BigOperators StatMech.Ising

instance {L : ℕ} (d : ons_Dart L) : Decidable (ons_xWrap d) := by
  unfold ons_xWrap
  infer_instance

instance {L : ℕ} (d : ons_Dart L) : Decidable (ons_yWrap d) := by
  unfold ons_yWrap
  infer_instance

end StatMech.Onsager

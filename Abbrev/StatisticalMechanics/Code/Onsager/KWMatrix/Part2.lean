/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWMatrix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Onsager.KWMatrix


namespace StatMech.Onsager

abbrev ons_Dart (L : ℕ) := (ZMod L × ZMod L) × Fin 4


end StatMech.Onsager

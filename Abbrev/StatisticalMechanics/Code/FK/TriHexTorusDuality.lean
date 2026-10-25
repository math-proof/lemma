/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

abbrev TorusSite (L : ℕ) := ZMod L × ZMod L

abbrev TriHexTorusEdgeIndex (L : ℕ) := TorusSite L × Fin 3

abbrev HexTorusVertex (L : ℕ) := TorusSite L × Bool

end PeriodicPlanar
end FK
end StatMech

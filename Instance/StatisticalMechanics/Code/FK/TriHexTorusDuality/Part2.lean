/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Def.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

noncomputable instance (L : ℕ) [Fact (2 < L)] :
    DecidableRel (triangularTorusGraph L).Adj := Classical.decRel _

end PeriodicPlanar
end FK
end StatMech

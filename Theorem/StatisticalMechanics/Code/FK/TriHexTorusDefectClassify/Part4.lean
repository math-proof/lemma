/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDefectClassify.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part10
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusConnected
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount.Part2
import Def.StatisticalMechanics.Code.FK.TriHexTorusDefectClassify.Part3
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open StatMech.Lattice

open StatMech.Onsager

@[simp] theorem triHexTorusCutDualGraph_adj (L : ℕ) [Fact (2 < L)]
    (S : Set (TorusSite L)) (f g : HexTorusVertex L) :
    (triHexTorusCutDualGraph L S).Adj f g ↔
      (hexagonalTorusGraph L).Adj f g ∧
        triHexTorusEdgeStraddles S
          (triHexTorusPrimalOfDualEdge L s(f, g)) := Iff.rfl

end PeriodicPlanar
end FK
end StatMech

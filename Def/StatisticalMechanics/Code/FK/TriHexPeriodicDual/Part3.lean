/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDuality
import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part3
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice

noncomputable def triangularEdgeChartEquiv :
    TriHexEdgeIndex ≃ triangularGraph.edgeSet :=
  Equiv.ofBijective triangularEdgeChart
    ⟨triangularEdgeChart_injective, triangularEdgeChart_surjective⟩

end PeriodicPlanar
end FK
end StatMech

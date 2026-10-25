/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part5
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Instance.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep
open Finset


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

noncomputable section

def triHexPlanarCellTerminal (z : Site 2) (i : Fin 3) : Site 2 :=
  z + hexagonalStep i


noncomputable def triHexPlanarFiniteTerminalFinset (n : Nat) : Finset (Site 2) :=
  (((box_finite 2 n).toFinset ×ˢ (Finset.univ : Finset (Fin 3))).image
    fun zi => triHexPlanarCellTerminal zi.1 zi.2)

end
end StatMech.FK.PeriodicPlanar

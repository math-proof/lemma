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
import Abbrev.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part2
open Finset


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

noncomputable section

noncomputable def triHexPlanarFiniteTerminalMap (n : Nat)
    (z : TriHexPlanarFiniteCell n) (i : Fin 3) :
    TriHexPlanarFiniteTerminal n := by
  refine ⟨triHexPlanarCellTerminal z.1 i, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨(z.1, i), ?_, rfl⟩
  apply Finset.mem_product.mpr
  exact ⟨by simpa using z.2, Finset.mem_univ i⟩


def triHexPlanarFiniteBoundary (n : Nat)
    (v : TriHexPlanarFiniteTerminal n) : Prop :=
  ∃ i : Fin 3, v.1 - hexagonalStep i ∉ box 2 n

end
end StatMech.FK.PeriodicPlanar

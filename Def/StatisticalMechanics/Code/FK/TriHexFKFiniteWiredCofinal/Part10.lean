/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDiagonalLimit
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverageUpgrade
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part10
open Finset Set SimpleGraph Filter MeasureTheory Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

def triHexPlanarFiniteTriangleToBuffered (n : Nat) :
    TriHexPlanarFiniteTerminal n ↪ triangular.BufferedVertex (n + 2) :=
  (Function.Embedding.refl (Site 2)).subtypeMap fun {v} hv => by
    apply triangular.orbitBox_mono
      ((Nat.succ_le_succ (Nat.le_succ n)).trans
        (triangular.id_le_bufferedRadius (n + 2)))
    exact triHexPlanarFiniteTerminal_subset_triangular_orbitBox_succ n ⟨v, hv⟩

end
end StatMech.FK.PeriodicPlanar

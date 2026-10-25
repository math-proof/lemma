/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part9
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def RlcCentralFaceMinimalReflectedCutPiece {n : Int}
    (S : Finset (Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n))) : Prop :=
  S.Nonempty ∧
    Ising.kwg_IsEven
      (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n)) S ∧
    ∀ T : Finset (Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)),
      T ⊆ S → T.Nonempty →
        Ising.kwg_IsEven
          (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n)) T →
        T = S


end
end StatMech.Universality

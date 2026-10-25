/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Def.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part3
open Finset SimpleGraph Set


namespace StatMech

namespace BeffaraDC

open Lattice Ising Walls


theorem pfd_numDualClusters_eq_faceComponents (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) (hKP : K ≤ P.G) :
    Nat.card (pfdClosedDual P K).ConnectedComponent =
      Nat.card (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent := by
  rw [Nat.card_congr (pfdComponentEquiv P K hKP)]


end BeffaraDC
end StatMech

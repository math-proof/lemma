/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part4
open Finset SimpleGraph Set


namespace StatMech

namespace BeffaraDC

open Lattice Ising Walls


noncomputable def pfdPrimalWeight (P : PlanarZ2Subgraph) (p q : ℝ)
    (K : SimpleGraph P.V) : ℝ :=
  edgeProductCount p P.G.edgeFinset.card K.edgeSet.ncard *
    q ^ Nat.card K.ConnectedComponent


noncomputable def pfdDualWeight (P : PlanarZ2Subgraph) (p q : ℝ)
    (K : SimpleGraph P.V) : ℝ :=
  edgeProductCount p P.G.edgeFinset.card
      (P.G.edgeFinset.card - K.edgeSet.ncard) *
    q ^ Nat.card (pfdClosedDual P K).ConnectedComponent

end BeffaraDC
end StatMech

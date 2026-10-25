/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part8
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

noncomputable def graphEdgeConfig {V : Type*} (K : SimpleGraph V) :
    ConfigSpace (Sym2 V) := by
  classical
  exact fun e => decide (e ∈ K.edgeSet)


noncomputable def triHexTorusFaceCount (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (TorusSite L)) : ℕ := by
  exact Nat.card (FK.openSub (hexagonalTorusGraph L)
    (triHexTorusDualConfig L (graphEdgeConfig K))).ConnectedComponent


noncomputable def triHexTorusDefect (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (TorusSite L)) : ℤ :=
  (K.edgeSet.ncard : ℤ) - Nat.card (TorusSite L) +
    Nat.card K.ConnectedComponent + 1 - triHexTorusFaceCount L K

end PeriodicPlanar
end FK
end StatMech

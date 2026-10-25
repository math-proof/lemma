/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOuterFaceUnique.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanOuterFaceUnique
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

noncomputable def outerRegion (P : PlanarZ2Subgraph) :
    (regionGraph (imageGraph P)).ConnectedComponent :=
  (regionGraph (imageGraph P)).connectedComponentMk (beacon 2 (outerBoxRadius P))


end Lattice
end StatMech

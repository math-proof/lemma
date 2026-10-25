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
import Theorem.StatisticalMechanics.Code.Lattice.JordanOuterFaceUnique.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

def boundedRegionEquivNeOuter (P : PlanarZ2Subgraph) :
    {C : (regionGraph (imageGraph P)).ConnectedComponent // C.supp.Finite} ≃
      {C : (regionGraph (imageGraph P)).ConnectedComponent // C ≠ outerRegion P} :=
  Equiv.subtypeEquivRight (boundedRegion_iff_ne_outer P)


end Lattice
end StatMech

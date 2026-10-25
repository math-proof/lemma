/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part7
open SimpleGraph Function


namespace StatMech

namespace Lattice

def OrbitKingTransport (K : Set (Site 2)) : Prop :=
  ∀ (e : Dart), IsBoundaryDart K e →
    ∀ {u v : Site 2}, u ∉ K → v ∉ K → KingAdj u v →
      OrbitReached K e u → OrbitReached K e v


def OrbitVertexSaturate (K : Set (Site 2)) : Prop :=
  ∀ (e : Dart), IsBoundaryDart K e → ∀ {v : Site 2}, OrbitReached K e v →
    ∀ d : Dart, IsBoundaryDart K d → d.head = v → SameOrbit K e d


def BoundaryKingConnected (K : Set (Site 2)) : Prop :=
  ∀ {u w : Site 2} (hu : u ∉ K) (hw : w ∉ K),
    ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨u, hu⟩ ⟨w, hw⟩ →
    (boundaryKingGraph K).Reachable ⟨u, hu⟩ ⟨w, hw⟩


end Lattice
end StatMech

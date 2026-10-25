/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedGlobal.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedProof
import Theorem.StatisticalMechanics.Code.Lattice.KingFacts
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedGlobal
open SimpleGraph Function


namespace StatMech

namespace Lattice

def OrbitTraceSurjective (K : Set (Site 2)) : Prop :=
  ∀ (e f : Dart) (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f),
    ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ →
    SameOrbit K e f


end Lattice
end StatMech

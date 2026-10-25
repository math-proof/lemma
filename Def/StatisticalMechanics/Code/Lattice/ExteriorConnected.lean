/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.InteriorOrientation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EnclosedAreaWitness.Part3
import Theorem.StatisticalMechanics.Code.Lattice.ExteriorConnected
open Set SimpleGraph


namespace StatMech

namespace Lattice

def exc_OffSupportReachesExterior (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    Prop :=
  ∃ R : ℕ, ∃ hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R,
    ∀ z, z ∉ K → z ∉ (mpl_orbitLoop K a).support →
      ∃ hz : z ∈ ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2))ᶜ,
        ∃ e : Site 2, ∃ he : e ∈ exterior 2 R,
          ((hypercubicLattice 2).induce
              ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2))ᶜ).Reachable
            ⟨z, hz⟩ ⟨e, exterior_subset_compl _ R hRbox he⟩


end Lattice
end StatMech

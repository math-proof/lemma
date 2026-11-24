module
public import Theorem.StatisticalMechanics.Code.Walls.kc6core.Part2
public import Theorem.StatisticalMechanics.Code.Walls.kc6uniqueinfinitecomponent
public import Theorem.StatisticalMechanics.Code.Walls.kc6localconstancy
public import Theorem.StatisticalMechanics.Code.Lattice.OutsideConnected.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.ExteriorConnected.Part3
public import Theorem.StatisticalMechanics.Code.Walls.kc7core
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc7core.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


def kc7_OffSupportOutsideInfinite (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∀ z, z ∉ K → z ∉ (mpl_orbitLoop K a).support →
    ∃ hzmem : z ∈ (oc_supportSet (mpl_orbitLoop K a))ᶜ,
      (((hypercubicLattice 2).induce (oc_supportSet (mpl_orbitLoop K a))ᶜ).connectedComponentMk
        ⟨z, hzmem⟩).supp.Infinite


end Walls
end StatMech

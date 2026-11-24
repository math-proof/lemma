module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.OutsideConnected.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.EnclosedAreaWitness.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.ExteriorConnected.Part3
public import Theorem.StatisticalMechanics.Code.Walls.kc3_offsupportreaches
public import Theorem.StatisticalMechanics.Code.Walls.kc4_eulerone.Part2
public import Theorem.StatisticalMechanics.Code.Walls.kc4_orbitiscycle
public import Theorem.StatisticalMechanics.Code.Walls.kc4_core
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_core.lean -/
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


def kc4_OutsideInInfiniteComponent (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∀ (z : Site 2), z ∉ jec_leftRegion Vc →
    ∃ hzmem : z ∈ (oc_supportSet Vc)ᶜ,
      (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
        ⟨z, hzmem⟩).supp.Infinite


end Walls
end StatMech

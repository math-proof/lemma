/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCoresUnify.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ArcSides.Part3
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanCoresUnify
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


def jcu_HasSeparatingSide (D B inside outside : Set (Site 2)) : Prop :=
  ∃ S : Set (Site 2),
    (∀ z ∈ inside, z ∈ S) ∧
    (∀ z ∈ outside, z ∉ S) ∧
    (∀ u v : Site 2, u ∈ D → v ∈ D → (hypercubicLattice 2).Adj u v →
      u ∈ S → v ∉ S → (u ∈ B ∨ v ∈ B))


end Lattice
end StatMech

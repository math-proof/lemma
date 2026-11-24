module
public import Mathlib
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
public import Theorem.StatisticalMechanics.Code.Universality.HVIntersection.Part2
public import Theorem.StatisticalMechanics.Code.Universality.VSeparatesFixed.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.ArcSides.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding
open Set SimpleGraph MeasureTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TwoPathsCrossWinding.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


def ArcSeparatingSet (P : Set (Site 2)) (α β c d : ℤ) : Prop :=
  ∃ S : Set (Site 2),
    (∀ z : Site 2, z ∈ rect α β c d → z 0 = α → z ∈ S) ∧
    (∀ z : Site 2, z ∈ rect α β c d → z 0 = β → z ∉ S) ∧
    (∀ u v : Site 2, u ∈ rect α β c d → v ∈ rect α β c d →
        (hypercubicLattice 2).Adj u v → bdEdge S s(u, v) → u ∈ P ∨ v ∈ P)


end Lattice
end StatMech

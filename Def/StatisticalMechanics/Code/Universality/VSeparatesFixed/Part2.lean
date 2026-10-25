/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/VSeparatesFixed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.Strip.Part2
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.RSWStrip.Part3
import Theorem.StatisticalMechanics.Code.Universality.HVIntersection.Part2
import Theorem.StatisticalMechanics.Code.Universality.VSeparates.Part2
import Theorem.StatisticalMechanics.Code.Universality.VSeparatesFixed
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


def vsFix_arc_sides (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ) : Prop :=
  α ≤ m → m ≤ m' → m' ≤ β →
  ∀ (xB : Site 2) (hxB : xB ∈ rect m m' c d),
  xB ∈ bottomSide m m' c d →
  ∀ (yT : Site 2) (hyT : yT ∈ topSide m m' c d),
  ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ ⟨yT, topSide_subset hyT⟩ →
  ∃ L : Set (Site 2),
    
    (∀ z : Site 2, z ∈ rect α β c d → z 0 = α → z ∈ L) ∧
    
    (∀ z : Site 2, z ∈ rect α β c d → z 0 = β → z ∉ L) ∧
    
    (∀ u v : Site 2, u ∈ rect α β c d → v ∈ rect α β c d →
        (hypercubicLattice 2).Adj u v → bdEdge L s(u, v) →
        u ∈ overlapComp ω m m' c d xB hxB ∨ v ∈ overlapComp ω m m' c d xB hxB)


end Universality
end StatMech

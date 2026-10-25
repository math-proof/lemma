/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcSides.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.HVIntersection.Part2
import Theorem.StatisticalMechanics.Code.Universality.VSeparatesFixed.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ArcSides.Part2
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


def ArcS_TwoPathsCross (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) : Prop :=
  α ≤ m → m ≤ m' → m' ≤ β →
  ∀ (x y : Site 2), x ∈ rect α β c d → y ∈ rect α β c d → x 0 = α → y 0 = β →
  ∀ (γ : (hypercubicLattice 2).Walk x y),
    (∀ z ∈ γ.support, z ∈ rect α β c d) →
    ∃ z ∈ γ.support, z ∈ overlapComp ω m m' c d xB hxB


end Lattice
end StatMech

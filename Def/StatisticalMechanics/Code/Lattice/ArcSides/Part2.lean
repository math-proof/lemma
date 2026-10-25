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
import Theorem.StatisticalMechanics.Code.Lattice.ArcSides
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


def floodFromLeft (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) : Set (Site 2) :=
  {z | ∃ x : Site 2, x ∈ rect α β c d ∧ x 0 = α ∧ x ∉ overlapComp ω m m' c d xB hxB ∧
        (boxMinusP ω α β m m' c d xB hxB).Reachable x z}


def arcS_leftRegion (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) : Set (Site 2) :=
  {z | z ∈ rect α β c d ∧ (z 0 = α ∨ z ∈ floodFromLeft ω α β m m' c d xB hxB)}

end Lattice
end StatMech

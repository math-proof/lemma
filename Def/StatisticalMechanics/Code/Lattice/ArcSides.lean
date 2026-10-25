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
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


noncomputable def boxMinusP (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) : SimpleGraph (Site 2) where
  Adj u v := (hypercubicLattice 2).Adj u v ∧ u ∈ rect α β c d ∧ v ∈ rect α β c d ∧
             u ∉ overlapComp ω m m' c d xB hxB ∧ v ∉ overlapComp ω m m' c d xB hxB
  symm := by constructor; intro u v ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1.symm, h3, h2, h5, h4⟩
  loopless := ⟨fun u h => (hypercubicLattice 2).irrefl h.1⟩

end Lattice
end StatMech

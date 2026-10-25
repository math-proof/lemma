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
import Def.StatisticalMechanics.Code.Lattice.ArcSides
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


@[simp] theorem boxMinusP_adj (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) (u v : Site 2) :
    (boxMinusP ω α β m m' c d xB hxB).Adj u v ↔
      (hypercubicLattice 2).Adj u v ∧ u ∈ rect α β c d ∧ v ∈ rect α β c d ∧
       u ∉ overlapComp ω m m' c d xB hxB ∧ v ∉ overlapComp ω m m' c d xB hxB := Iff.rfl


theorem boxMinusP_le (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) :
    boxMinusP ω α β m m' c d xB hxB ≤ hypercubicLattice 2 := fun _ _ h => h.1


theorem boxMinusP_walk_dest (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) {x z : Site 2}
    (hx : x ∈ rect α β c d) (hxP : x ∉ overlapComp ω m m' c d xB hxB)
    (w : (boxMinusP ω α β m m' c d xB hxB).Walk x z) :
    z ∈ rect α β c d ∧ z ∉ overlapComp ω m m' c d xB hxB := by
  induction w with
  | nil => exact ⟨hx, hxP⟩
  | @cons a b e hab p ih => exact ih hab.2.2.1 hab.2.2.2.2


end Lattice
end StatMech

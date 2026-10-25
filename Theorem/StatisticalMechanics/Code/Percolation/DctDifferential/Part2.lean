/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.Percolation.DctDifferential.Part2
open MeasureTheory Function Set
open scoped NNReal
open StatMech


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


theorem mem_boxEdgeFinset {d n : ℕ} {e : Sym2 (Site d)} :
    e ∈ boxEdgeFinset d n ↔ ∃ x y, x ∈ box d n ∧ y ∈ box d n ∧ e = s(x, y) := by
  simp only [boxEdgeFinset, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, he⟩
    exact ⟨x, y, by simpa using hx, by simpa using hy, he.symm⟩
  · rintro ⟨x, y, hx, hy, rfl⟩
    exact ⟨(x, y), ⟨by simpa using hx, by simpa using hy⟩, rfl⟩


theorem coord_of_agree (n : ℕ) {ω ω' : ConfigSpace (Sym2 (Site d))}
    (h : ∀ e ∈ (boxEdgeFinset d n : Set (Sym2 (Site d))), ω e = ω' e)
    (x y : Site d) (hx : x ∈ box d n) (hy : y ∈ box d n) : ω s(x, y) = ω' s(x, y) := by
  apply h
  simp only [boxEdgeFinset, Finset.coe_image, Finset.coe_product, Set.mem_image, Set.mem_prod]
  exact ⟨(x, y), ⟨by simp [hx], by simp [hy]⟩, rfl⟩


end Percolation
end StatMech

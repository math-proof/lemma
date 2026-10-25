/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BoxMergeFreeMenger.Part2
import Def.StatisticalMechanics.Code.Percolation.TrifurcationExistence2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem tex_threeDistinctInfinite_of_threeMeetBox {n : ℕ}
    {ω : ConfigSpace (Sym2 (Site d))} (hω : ω ∈ threeMeetBox d n) :
    tex_ThreeDistinctInfinite ω := by
  obtain ⟨_, x₁, x₂, x₃, _, _, _, hi1, hi2, hi3, hd12, hd13, hd23⟩ := hω
  exact ⟨x₁, x₂, x₃, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩


end Percolation
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagPercoIdBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.IsingFK.EsInfinite.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.FvES.Part4
import Theorem.StatisticalMechanics.Code.FK.TailLimit.Part2
import Theorem.StatisticalMechanics.Code.Ising.TransitionRegime
import Def.StatisticalMechanics.Code.IsingFK.MagPercoIdBox
open MeasureTheory Filter Topology
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.Ising StatMech.FK StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


theorem boxBoundary_nonempty (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    ∃ v : boxVerts d n, boxBoundary d n v := by
  classical
  have hd0 : (0 : ℕ) < d := hd
  let i0 : Fin d := ⟨0, hd0⟩
  let w : Site d := fun i => if i = i0 then (n : ℤ) else 0
  have hwbox : w ∈ box d n := by
    intro i
    by_cases h : i = i0
    · simp only [w, if_pos h, Int.natAbs_natCast]
      exact le_refl n
    · simp only [w, if_neg h, Int.natAbs_zero]; exact Nat.zero_le n
  have hwnotbox : w ∉ box d (n - 1) := by
    rw [mem_box, not_forall]
    refine ⟨i0, ?_⟩
    simp only [w, if_pos rfl, Int.natAbs_natCast, not_le]
    omega
  exact ⟨⟨w, hwbox⟩, by rw [boxBoundary]; exact ⟨hwbox, hwnotbox⟩⟩


end IsingFK
end StatMech

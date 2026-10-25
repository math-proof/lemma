/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/HisingBoxClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
import Theorem.StatisticalMechanics.Code.Lattice.ClusterContourBijection.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.MagnetizationCorrespondence
import Def.StatisticalMechanics.Code.IsingFK.HisingBoxClose
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.Ising StatMech.FK StatMech.Lattice StatMech.Percolation

variable {d n : ℕ}


@[simp] theorem hbx_fToB_bToF (b : Bool) : fToB (bToF b) = b := by
  unfold fToB bToF; cases b <;> decide

@[simp] theorem hbx_bToF_fToB (a : Fin 2) : bToF (fToB a) = a := by
  unfold fToB bToF; fin_cases a <;> decide


theorem hbx_boxBoundary_succ_iff (d n : ℕ) (v : boxVerts d (n + 1)) :
    boxBoundary d (n + 1) v ↔ (v : Site d) ∉ box d n := by
  rw [boxBoundary, mem_vertexBoundary]; simp only [Nat.add_sub_cancel]
  exact ⟨fun h => h.2, fun h => ⟨v.2, h⟩⟩


end IsingFK
end StatMech

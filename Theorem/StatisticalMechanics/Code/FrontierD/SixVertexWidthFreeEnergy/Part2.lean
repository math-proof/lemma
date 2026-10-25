/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWidthFreeEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFreeEnergy
import Def.StatisticalMechanics.Code.FrontierD.SixVertexWidthFreeEnergy
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

theorem sixVertexWidthSectorTopEigenvalue_le (N : ℕ) (c : ℝ)
    (n : Fin (N + 1)) :
    sixVertexWidthSectorTopEigenvalue N c n ≤ sixVertexWidthTopEigenvalue N c := by
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨n, Finset.mem_univ n, rfl⟩)

theorem sixVertexWidthTopEigenvalue_exists_sector (N : ℕ) (c : ℝ) :
    ∃ n : Fin (N + 1),
      sixVertexWidthSectorTopEigenvalue N c n = sixVertexWidthTopEigenvalue N c := by
  obtain ⟨n, hn, hmax⟩ := Finset.mem_image.mp
    (Finset.max'_mem (Finset.univ.image (sixVertexWidthSectorTopEigenvalue N c)) _)
  exact ⟨n, hmax⟩

theorem sixVertexWidthTopEigenvalue_pos (N : ℕ) {c : ℝ} (hc : 0 < c) :
    0 < sixVertexWidthTopEigenvalue N c := by
  let n : Fin (N + 1) := ⟨0, Nat.zero_lt_succ N⟩
  exact lt_of_lt_of_le
    (sixVertexSectorTopEigenvalue_pos (sixVertexWidthSectorIndex_le N n) hc)
    (sixVertexWidthSectorTopEigenvalue_le N c n)


end StatMech.FrontierD

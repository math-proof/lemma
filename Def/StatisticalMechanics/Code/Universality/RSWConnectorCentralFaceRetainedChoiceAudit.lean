/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_rca_rv : Fin 10 → rect 0 4 (-2) 2
  | 0 => ⟨![0, -2], by simp [mem_rect]⟩
  | 1 => ⟨![1, -2], by simp [mem_rect]⟩
  | 2 => ⟨![2, -2], by simp [mem_rect]⟩
  | 3 => ⟨![2, -1], by simp [mem_rect]⟩
  | 4 => ⟨![2, 0], by simp [mem_rect]⟩
  | 5 => ⟨![1, 0], by simp [mem_rect]⟩
  | 6 => ⟨![1, 1], by simp [mem_rect]⟩
  | 7 => ⟨![2, 1], by simp [mem_rect]⟩
  | 8 => ⟨![3, 1], by simp [mem_rect]⟩
  | 9 => ⟨![4, 1], by simp [mem_rect]⟩

end
end StatMech.Universality

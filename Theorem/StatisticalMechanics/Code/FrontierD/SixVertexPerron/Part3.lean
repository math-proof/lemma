/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part2
open Finset Matrix


namespace StatMech.FrontierD

theorem sixVertexForwardInterlaced_of_positions {N n : ℕ}
    (x y : SixVertexSector N n) (h : SixVertexPositionsForwardInterlaced x y) :
    SixVertexForwardInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y) := by
  constructor
  · simp
  · rw [sixVertexAlternating, sixVertexSector_upPositions_eq_map_position,
      sixVertexSector_upPositions_eq_map_position, zip_map_same]
    simp only [List.flatMap_map]
    apply pairwise_flatMap_pairs
    · intro i hi
      exact h.1 i
    · refine List.Pairwise.imp (l := List.finRange n) ?_ (List.sortedLT_finRange n).pairwise
      intro i j hij
      have hij' : i.val + 1 ≤ j.val := by omega
      have hi : i.val + 1 < n := lt_of_le_of_lt hij' j.prop
      calc
        sixVertexSectorPosition y i =
            sixVertexSectorPosition y ⟨i.val, by omega⟩ := by congr
        _ ≤ sixVertexSectorPosition x ⟨i.val + 1, hi⟩ := h.2 i.val hi
        _ ≤ sixVertexSectorPosition x j :=
          (sixVertexSectorPosition x).monotone (by simpa using hij')

theorem fin_val_le_of_strictMono {N n : ℕ} (f : Fin n → Fin N)
    (hf : StrictMono f) (i : Fin n) : i.val ≤ (f i).val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n =>
      induction i using Fin.induction with
      | zero => exact Nat.zero_le _
      | succ i ih =>
          have hlt : (f i.castSucc).val < (f i.succ).val := by
            exact_mod_cast hf (Fin.castSucc_lt_succ (i := i))
          simpa using Nat.succ_le_of_lt (lt_of_le_of_lt ih hlt)


end StatMech.FrontierD

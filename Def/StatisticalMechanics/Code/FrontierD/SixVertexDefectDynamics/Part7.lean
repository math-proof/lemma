/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part13
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics.Part6
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexShiftLeftEmbedding
    {N n : Nat} (x : SixVertexSector N n) (hn : 0 < n)
    (hfirst : 0 < (sixVertexSectorPosition x ⟨0, hn⟩).val) :
    Fin n ↪o Fin N := by
  let f : Fin n → Fin N := fun i =>
    ⟨(sixVertexSectorPosition x i).val - 1, by
      exact lt_of_le_of_lt (Nat.sub_le _ _) (sixVertexSectorPosition x i).isLt⟩
  exact OrderEmbedding.ofStrictMono f (by
    intro i j hij
    change (sixVertexSectorPosition x i).val - 1 <
      (sixVertexSectorPosition x j).val - 1
    have hmono := (sixVertexSectorPosition x).strictMono hij
    have hfirstLe : (sixVertexSectorPosition x ⟨0, hn⟩).val ≤
        (sixVertexSectorPosition x i).val := by
      exact Fin.le_iff_val_le_val.mp ((sixVertexSectorPosition x).monotone
        ((Fin.mk_le_mk).mpr (Nat.zero_le _)))
    omega)


def sixVertexShiftLeftSector
    {N n : Nat} (x : SixVertexSector N n) (hn : 0 < n)
    (hfirst : 0 < (sixVertexSectorPosition x ⟨0, hn⟩).val) :
    SixVertexSector N n :=
  Set.powersetCard.ofFinEmbEquiv
    (sixVertexShiftLeftEmbedding x hn hfirst)

end
end StatMech.FrontierD

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBetheOne.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBethe.Part6
import Def.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBetheOne
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexSectorPosition_singleton {N : ℕ} (i : Fin N) :
    sixVertexSectorPosition (sixVertexSingletonSector i) 0 = i := by
  have hmem := sixVertexSectorPosition_mem (sixVertexSingletonSector i) (0 : Fin 1)
  simpa [sixVertexSingletonSector] using hmem

theorem sixVertexSector_eq_singleton_position {N : ℕ}
    (x : SixVertexSector N 1) :
    x = sixVertexSingletonSector (sixVertexSectorPosition x 0) := by
  apply Subtype.ext
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp x.prop
  have hmem := sixVertexSectorPosition_mem x (0 : Fin 1)
  have hpos : sixVertexSectorPosition x 0 = i := by simpa [hi] using hmem
  simp [sixVertexSingletonSector, hi, hpos]


end
end StatMech.FrontierD

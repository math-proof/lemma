/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowAutomaton.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourParameterCompleteness.Part3


namespace StatMech.FrontierD

theorem sixVertexFourByFourAudited_validParameterSet_eq_coordinateImage :
    sixVertexFourByFourAuditedValidParameterSet =
      sixVertexFourByFourAuditedCoordinateParameterImage := by
  classical
  ext p
  simp only [sixVertexFourByFourAuditedValidParameterSet,
    Finset.mem_filter, Finset.mem_univ, true_and,
    sixVertexFourByFourAuditedCoordinateParameterImage, Finset.mem_image]
  constructor
  · intro hvalid
    obtain ⟨c, hc, _⟩ :=
      sixVertexFourByFourAudited_parameterValid_uniqueCoordinate p hvalid
    exact ⟨c, hc⟩
  · rintro ⟨c, rfl⟩
    exact sixVertexFourByFourAudited_coordinateParameters_valid c

theorem sixVertexFourByFourAudited_validParameterSet_card :
    sixVertexFourByFourAuditedValidParameterSet.card = 512 := by
  rw [sixVertexFourByFourAudited_validParameterSet_eq_coordinateImage]
  exact sixVertexFourByFourAuditedCoordinateParameterImage_card


end StatMech.FrontierD

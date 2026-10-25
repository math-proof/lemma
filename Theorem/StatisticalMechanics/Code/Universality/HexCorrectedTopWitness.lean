/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedTopWitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedHighestCut.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hexCSTopOne_legal :
    (ofTurns hexAWStart 1 [1, -1]).IsLegalSAW := by
  constructor
  · simp [HexWalk.LegalTurns]
  · simp [HexWalk.IsSAW, HexWalk.vertices, HexWalk.ofTurns,
      HexWalk.verticesAux]
    constructor
    · constructor
      · intro h
        have hz : (2 : ℂ) * halfStep 2 = 0 := by
          linear_combination -h
        exact (mul_ne_zero (by norm_num) (hexConcrete_halfStep_ne 2)) hz
      · intro h
        have hz : halfStep 1 + halfStep 2 = 0 := by
          linear_combination (-1 / 2 : ℂ) * h
        exact hexW1_halfStep_add_ne_zero 1 1 (Or.inl rfl) hz
    · intro h
      have hz : (2 : ℂ) * halfStep 1 = 0 := by
        linear_combination -h
      exact (mul_ne_zero (by norm_num) (hexConcrete_halfStep_ne 1)) hz

theorem hexCSTopOne_prefix_zero :
    hlhc_prefixCoord [1, -1] hexCSTopOne_legal.1 0 =
      hexAWOriginCoord := by
  apply hexAWPos_injective
  rw [← hlhc_prefixCoord_vertex [1, -1] hexCSTopOne_legal.1 0]
  simp only [List.take_zero, hexInfra_midAccum_nil,
    hexInfra_headAccum_nil, hexAWPos_origin]
  unfold hexAWStart halfStep
  rw [show (4 : ℤ) = 1 + 3 by norm_num, hexUnit_add_three]
  ring

theorem hexCSTopOne_prefix_one :
    hlhc_prefixCoord [1, -1] hexCSTopOne_legal.1 1 =
      ⟨0, -1, .white⟩ := by
  apply hexAWPos_injective
  rw [← hlhc_prefixCoord_vertex [1, -1] hexCSTopOne_legal.1 1]
  simp only [List.take, hexInfra_midAccum_cons, hexInfra_midAccum_nil,
    hexInfra_headAccum_cons, hexInfra_headAccum_nil]
  unfold hexAWStart hexAWPos hexAWBasisJ hexAWAxis halfStep
  rw [show (4 : ℤ) = 1 + 3 by norm_num, hexUnit_add_three]
  ring

end
end StatMech.Universality

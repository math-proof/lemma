/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part6


namespace StatMech.Universality

open HexWalk


theorem hlha_emptyAugment_isLegalSAW :
    (ofTurns 0 0 hlha_emptyAugment).IsLegalSAW := by
  simpa [hlha_emptyAugment] using hexWall3_isLegalSAW_witness (0 : ℂ)

theorem hlha_emptyAugment_halfSpace :
    HLHRLiteralHalfSpace 0 hlha_emptyAugment := by
  intro k hk hkle
  have hk1 : k = 1 := by
    simp only [hlha_emptyAugment, List.length_singleton] at hkle
    omega
  subst k
  have hturns := hlha_emptyAugment_isLegalSAW.1
  rw [hlhr_height_eq_latticeHeight _ hturns 0,
    hlhr_height_eq_latticeHeight _ hturns 1]
  norm_num [hlhr_latticeHeight, hlha_emptyAugment, hlhr_coordRun,
    HexReturnCoord.base, HexReturnCoord.turn, HexReturnCoord.right,
    HexReturnCoord.add, HexReturnCoord.zero]

@[simp] theorem hlha_emptyAugment_length : hlha_emptyAugment.length = 1 := rfl

end StatMech.Universality

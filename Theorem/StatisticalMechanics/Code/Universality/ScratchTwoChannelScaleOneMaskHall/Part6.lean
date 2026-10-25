/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part9


namespace StatMech.Universality

theorem rlcScaleOneCodeA_ne_codeB (a : Fin 14 → Bool)
    (b : Fin 12 → Bool) : rlcScaleOneCodeA a ≠ rlcScaleOneCodeB b := by
  intro h
  have h8 := congrFun h (8 : Fin 16)
  simp [rlcScaleOneCodeA, rlcScaleOneCodeB] at h8

theorem rlcScaleOneCodeA_ne_codeC (a : Fin 14 → Bool)
    (c : Fin 11 → Bool) : rlcScaleOneCodeA a ≠ rlcScaleOneCodeC c := by
  intro h
  have h8 := congrFun h (8 : Fin 16)
  simp [rlcScaleOneCodeA, rlcScaleOneCodeC] at h8

theorem rlcScaleOneCodeA_ne_codeD (a : Fin 14 → Bool)
    (d : Fin 12 → Bool) : rlcScaleOneCodeA a ≠ rlcScaleOneCodeD d := by
  intro h
  have h7 := congrFun h (7 : Fin 16)
  simp [rlcScaleOneCodeA, rlcScaleOneCodeD] at h7

theorem rlcScaleOneCodeB_ne_codeC (b : Fin 12 → Bool)
    (c : Fin 11 → Bool) : rlcScaleOneCodeB b ≠ rlcScaleOneCodeC c := by
  intro h
  have h2 := congrFun h (2 : Fin 16)
  simp [rlcScaleOneCodeB, rlcScaleOneCodeC] at h2

theorem rlcScaleOneCodeB_ne_codeD (b d : Fin 12 → Bool) :
    rlcScaleOneCodeB b ≠ rlcScaleOneCodeD d := by
  intro h
  have h7 := congrFun h (7 : Fin 16)
  simp [rlcScaleOneCodeB, rlcScaleOneCodeD] at h7

theorem rlcScaleOneCodeC_ne_codeD (c : Fin 11 → Bool)
    (d : Fin 12 → Bool) : rlcScaleOneCodeC c ≠ rlcScaleOneCodeD d := by
  intro h
  have h7 := congrFun h (7 : Fin 16)
  simp [rlcScaleOneCodeC, rlcScaleOneCodeD] at h7

end StatMech.Universality

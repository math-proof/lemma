/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexEnum.Part6


namespace StatMech.Universality

open Complex

open HexWalk


noncomputable def HexVertexEnumeration.empty (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hzero : ∀ z, parafObservable region a h0 z (5/8) hexChi = 0) :
    HexVertexEnumeration region a h0 v du where
  pairs := ∅
  pairBase := fun _ => []
  pairLq := fun _ => []
  pairLr := fun _ => []
  pairLq_sum := by simp
  pairLr_sum := by simp
  pairLen := by simp
  pairQ_valid := by simp
  pairR_valid := by simp
  triplets := ∅
  tripBase := fun _ => []
  tripP_valid := by simp
  tripQ_valid := by simp
  tripR_valid := by simp
  reindex := by simp [hzero]

end StatMech.Universality

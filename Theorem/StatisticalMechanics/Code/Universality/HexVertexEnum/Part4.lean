/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Structure.StatisticalMechanics.Code.Universality.HexVertexEnum


namespace StatMech.Universality

open Complex

open HexWalk


namespace HexVertexEnumeration

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


theorem relation (E : HexVertexEnumeration region a h0 v du) :
    ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 := by
  rw [E.reindex]
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro T hT
    exact genuine_triplet_zero region a h0 v du (E.tripBase T)
      (E.tripP_valid T hT) (E.tripQ_valid T hT) (E.tripR_valid T hT)
  · intro P hP
    exact genuine_pair_zero region a h0 v du (E.pairBase P) (E.pairLq P) (E.pairLr P)
      (E.pairLq_sum P hP) (E.pairLr_sum P hP) (E.pairLen P hP)
      (E.pairQ_valid P hP) (E.pairR_valid P hP)


end HexVertexEnumeration
end StatMech.Universality

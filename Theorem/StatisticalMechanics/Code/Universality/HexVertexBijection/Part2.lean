/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexEnum.Part5
import Structure.StatisticalMechanics.Code.Universality.HexVertexBijection


namespace StatMech.Universality

open Complex

open Function

open HexWalk


variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


namespace HexVertexBijection

variable (B : HexVertexBijection region a h0 v du)


theorem hinj :
    Function.Injective
      fun x : Function.support (combinedSummand region a h0 v du ∘ B.enum.slotTurns) =>
        B.enum.slotTurns x.1 :=
  hinj_of_leftInverse B.enum B.classify B.classify_slotTurns


theorem hsub :
    Function.support (combinedSummand region a h0 v du) ⊆
      Set.range fun x : Function.support (combinedSummand region a h0 v du ∘ B.enum.slotTurns) =>
        B.enum.slotTurns x.1 :=
  hsub_of_rightInverse B.enum B.classify B.slotTurns_classify


theorem relation (B : HexVertexBijection region a h0 v du) (hdu : du ≠ 0)
    (hp : Summable fun ts => parafSummand region a h0 (v + du) (5/8) hexChi ts)
    (hq : Summable fun ts => parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts)
    (hr : Summable fun ts => parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts) :
    ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 :=
  HexVertexEnumeration.relation_of_bijection B.enum hdu hp hq hr B.hinj B.hsub

end HexVertexBijection
end StatMech.Universality

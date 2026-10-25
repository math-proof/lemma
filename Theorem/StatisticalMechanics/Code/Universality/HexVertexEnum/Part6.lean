/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexEnum.Part4


namespace StatMech.Universality

open Complex

open HexWalk


namespace HexVertexEnumeration

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


theorem tsum_combinedSummand_slot_eq_zero (E : HexVertexEnumeration region a h0 v du)
    (hdu : du ≠ 0) :
    ∑' slot, combinedSummand region a h0 v du (slotTurns E slot) = 0 := by
  rw [tsum_fintype, Fintype.sum_sum_type]
  have h1 : ∑ x : E.pairs × Bool,
      combinedSummand region a h0 v du (slotTurns E (Sum.inl x)) = 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    rintro ⟨P, hP⟩ _
    rw [Fintype.sum_bool]
    
    show combinedSummand region a h0 v du (E.pairBase P ++ E.pairLr P)
        + combinedSummand region a h0 v du (E.pairBase P ++ E.pairLq P) = 0
    rw [combinedSummand_at_r (du := du) hdu (E.pairR_valid P hP).2.2,
        combinedSummand_at_q (du := du) hdu (E.pairQ_valid P hP).2.2]
    rw [add_comm]
    exact genuine_pair_zero region a h0 v du (E.pairBase P) (E.pairLq P) (E.pairLr P)
      (E.pairLq_sum P hP) (E.pairLr_sum P hP) (E.pairLen P hP)
      (E.pairQ_valid P hP) (E.pairR_valid P hP)
  have h2 : ∑ x : E.triplets × Fin 3,
      combinedSummand region a h0 v du (slotTurns E (Sum.inr x)) = 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    rintro ⟨T, hT⟩ _
    rw [Fin.sum_univ_three]
    show combinedSummand region a h0 v du (E.tripBase T)
        + combinedSummand region a h0 v du (E.tripBase T ++ [-1])
        + combinedSummand region a h0 v du (E.tripBase T ++ [1]) = 0
    rw [combinedSummand_at_p (du := du) hdu (E.tripP_valid T hT).2.2,
        combinedSummand_at_q (du := du) hdu (E.tripQ_valid T hT).2.2,
        combinedSummand_at_r (du := du) hdu (E.tripR_valid T hT).2.2]
    exact genuine_triplet_zero region a h0 v du (E.tripBase T)
      (E.tripP_valid T hT) (E.tripQ_valid T hT) (E.tripR_valid T hT)
  rw [h1, h2, add_zero]


theorem relation_of_bijection (E : HexVertexEnumeration region a h0 v du)
    (hdu : du ≠ 0)
    (hp : Summable fun ts => parafSummand region a h0 (v + du) (5/8) hexChi ts)
    (hq : Summable fun ts => parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts)
    (hr : Summable fun ts => parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts)
    (hinj : Function.Injective
      fun x : Function.support (combinedSummand region a h0 v du ∘ slotTurns E) =>
        slotTurns E x.1)
    (hsub : Function.support (combinedSummand region a h0 v du) ⊆
      Set.range fun x : Function.support (combinedSummand region a h0 v du ∘ slotTurns E) =>
        slotTurns E x.1) :
    ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 := by
  rw [vertexSum_eq_tsum_combinedSummand region a h0 v du hp hq hr]
  
  rw [tsum_eq_tsum_of_ne_zero_bij
        (g := combinedSummand region a h0 v du ∘ slotTurns E)
        (fun x => slotTurns E x.1) hinj hsub (fun _ => rfl)]
  
  exact tsum_combinedSummand_slot_eq_zero E hdu

end HexVertexEnumeration
end StatMech.Universality

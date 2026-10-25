/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryGeometry
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem FKIsingSquarePerimeterOppositeCarrierSwitchingAt.paired_summand
    {n : Nat} {hn : 0 < n} {side : FKIsingSquareBoundarySide}
    {k : Fin (2 * n)}
    (S : FKIsingSquarePerimeterOppositeCarrierSwitchingAt n hn side k)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand
        (S.pairing omega)
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterCancelledSide side)) =
      -(fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand omega
        S.mate := by
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquarePerimeterCancelledSide side)
  change D.fermionicSummand (S.pairing omega) z =
    -D.fermionicSummand omega S.mate
  unfold FKIsingDobrushinDomain.fermionicSummand
  by_cases hm : S.mate ∈ D.exploration omega
  · have hz : z ∈ D.exploration (S.pairing omega) :=
      (S.visited omega).2 hm
    rw [if_pos hz, if_pos hm, S.mass omega, S.phase omega hm]
    ring
  · have hz : z ∉ D.exploration (S.pairing omega) :=
      fun h ↦ hm ((S.visited omega).1 h)
    rw [if_neg hz, if_neg hm, neg_zero]


theorem FKIsingSquarePerimeterOppositeCarrierSwitchingAt.observable_eq_neg_mate
    {n : Nat} {hn : 0 < n} {side : FKIsingSquareBoundarySide}
    {k : Fin (2 * n)}
    (S : FKIsingSquarePerimeterOppositeCarrierSwitchingAt n hn side k) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterCancelledSide side)) =
      -(fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable S.mate := by
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquarePerimeterCancelledSide side)
  unfold FKIsingDobrushinDomain.fermionicObservable
  calc
    ∑ omega, D.fermionicSummand omega z =
        ∑ omega, D.fermionicSummand (S.pairing omega) z := by
      exact (S.pairing.sum_comp (fun omega ↦ D.fermionicSummand omega z)).symm
    _ = ∑ omega, -D.fermionicSummand omega S.mate := by
      apply Finset.sum_congr rfl
      intro omega _
      exact S.paired_summand omega
    _ = -∑ omega, D.fermionicSummand omega S.mate := by simp


theorem FKIsingSquarePerimeterOppositeCarrierSwitchingAt.cancellationAt_of_transport
    {n : Nat} {hn : 0 < n} {side : FKIsingSquareBoundarySide}
    {k : Fin (2 * n)}
    (S : FKIsingSquarePerimeterOppositeCarrierSwitchingAt n hn side k)
    (htransport :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable S.mate =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquarePerimeterCancelledSide side))) :
    FKIsingSquarePerimeterCancellationAt n hn side k := by
  refine ⟨S.uncut, ?_⟩
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquarePerimeterCancelledSide side)
  have hneg : D.fermionicObservable z = -D.fermionicObservable z := by
    calc
      D.fermionicObservable z = -D.fermionicObservable S.mate := by
        simpa only [D, z] using S.observable_eq_neg_mate
      _ = -D.fermionicObservable z := by
        exact congrArg Neg.neg (by simpa only [D, z] using htransport)
  have htwo : (2 : Complex) * D.fermionicObservable z = 0 := by
    linear_combination hneg
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

end
end StatMech.Universality

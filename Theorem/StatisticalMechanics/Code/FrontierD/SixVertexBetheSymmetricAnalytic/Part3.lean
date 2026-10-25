/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic.Part8
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricAnalytic.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBetheResidual_symmetric
    {N n : Nat} {c : Real} {p : Fin n → Real}
    (hp : SixVertexRootSymmetric p) :
    SixVertexRootSymmetric (fun j => sixVertexBetheResidual c N n p j) := by
  intro j
  have hsum :
      (∑ k : Fin n, sixVertexTheta c (p j.rev) (p k)) =
        -(∑ k : Fin n, sixVertexTheta c (p j) (p k)) := by
    calc
      (∑ k : Fin n, sixVertexTheta c (p j.rev) (p k)) =
          ∑ k : Fin n, sixVertexTheta c (-p j) (-p k.rev) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [hp j]
            simp [hp k]
      _ = ∑ k : Fin n, -sixVertexTheta c (p j) (p k.rev) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [sixVertexTheta_neg]
      _ = -(∑ k : Fin n, sixVertexTheta c (p j) (p k)) := by
            rw [Finset.sum_neg_distrib]
            congr 1
            apply Fintype.sum_equiv Fin.revPerm
            intro k
            rfl
  change (N : Real) * p j.rev +
      (∑ k, sixVertexTheta c (p j.rev) (p k)) -
        2 * Real.pi * sixVertexCentralQuantumNumber j.rev =
    -((N : Real) * p j +
      (∑ k, sixVertexTheta c (p j) (p k)) -
        2 * Real.pi * sixVertexCentralQuantumNumber j)
  rw [hsum, hp, sixVertexCentralQuantumNumber_rev]
  ring

theorem sixVertexEvenSymmetricBetheResidual_eq_zero_iff
    (N m : Nat) (c : Real) (q : Fin m → Real) :
    sixVertexEvenSymmetricBetheResidual N m c q = 0 ↔
      SixVertexSatisfiesBetheEquations c N (m + m)
        (sixVertexEvenSymmetricLift m q) := by
  constructor
  · intro h
    apply (sixVertexBetheResidual_eq_zero_iff c N (m + m)
      (sixVertexEvenSymmetricLift m q)).1
    intro i
    refine Fin.addCases ?_ ?_ i <;> intro j
    · have hsymm := sixVertexBetheResidual_symmetric (N := N) (c := c)
          (sixVertexEvenSymmetricLift_symmetric m q) (Fin.natAdd m j.rev)
      have hzero : sixVertexBetheResidual c N (m + m)
          (sixVertexEvenSymmetricLift m q) (Fin.natAdd m j.rev) = 0 := by
        simpa [sixVertexEvenSymmetricBetheResidual] using congrFun h j.rev
      have hrev : (Fin.natAdd m j.rev).rev = Fin.castAdd m j := by
        apply Fin.ext
        simp [Fin.rev, Fin.natAdd, Fin.castAdd]
        omega
      rw [hrev] at hsymm
      have hrel : sixVertexBetheResidual c N (m + m)
          (sixVertexEvenSymmetricLift m q) (Fin.castAdd m j) =
          -sixVertexBetheResidual c N (m + m)
            (sixVertexEvenSymmetricLift m q) (Fin.natAdd m j.rev) := by
        simpa only using hsymm
      rw [hrel, hzero, neg_zero]
    · exact congrFun h j
  · intro h
    funext j
    exact (sixVertexBetheResidual_eq_zero_iff c N (m + m)
      (sixVertexEvenSymmetricLift m q)).2 h (Fin.natAdd m j)


end
end StatMech.FrontierD

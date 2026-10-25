/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBetheOne.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhase
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBetheCollisionFreeIntervalSum_zeroPhase
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) -> Real)
    (x : Fin (n + 1) -> Int) (ell : Fin (n + 1)) (hell : p ell = 0)
    (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i < x i) :
    sixVertexBetheCollisionFreeIntervalSum N c
        (fun i => sixVertexBethePhase (p i)) x =
      sixVertexBetheZeroPhaseRegularizedIntervalSum N c p x ell := by
  classical
  unfold sixVertexBetheZeroPhaseRegularizedIntervalSum
  rw [sixVertexBetheCollisionFreeIntervalSum_inclusionExclusion]
  let P := (Finset.univ : Finset (Fin (n + 1))).powerset
  let Q := sixVertexBetheNoAdjacentCollisionSets n
  calc
    (∑ S ∈ P, (-1 : Complex) ^ S.card *
        sixVertexBetheCollisionConstrainedIntervalSum N c
          (fun i => sixVertexBethePhase (p i)) x S) =
      ∑ S ∈ Q, (-1 : Complex) ^ S.card *
        sixVertexBetheCollisionConstrainedIntervalSum N c
          (fun i => sixVertexBethePhase (p i)) x S := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro S hSP hSQ
        have hnS : ¬ SixVertexBetheNoAdjacent S := by
          simpa [Q, sixVertexBetheNoAdjacentCollisionSets, P, hSP] using hSQ
        rw [sixVertexBetheCollisionConstrainedIntervalSum_zero_of_adjacent
          N c _ x S hgap hnS, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S hS
      have hno : SixVertexBetheNoAdjacent S := by
        simpa [Q, sixVertexBetheNoAdjacentCollisionSets, P] using hS
      rw [sixVertexBetheCollisionConstrainedIntervalSum_zeroPhase
        N c p x S ell hell hno hgap]


theorem SixVertexSatisfiesMultiplicativeBetheEquations.physicalZeroPhaseIntervalExpansion
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) -> Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (ell : Fin (n + 1)) (hell : p ell = 0)
    (x : SixVertexSector N (n + 1)) :
    (sixVertexSectorTransferComplex N (n + 1) c).mulVec
        (sixVertexCoordinateBetheWave c p) x =
      ∑ sigma : Equiv.Perm (Fin (n + 1)),
        sixVertexBetheAmplitude c p sigma *
          sixVertexBetheZeroPhaseRegularizedIntervalSum N c
            (fun i => p (sigma i)) (sixVertexSectorIntCoordinates x)
            (sigma.symm ell) := by
  rw [hp.physicalCyclicIntervalExpansion hc p x]
  let Q := sixVertexBetheCollisionFreeTuples N
    (sixVertexSectorIntCoordinates x)
  calc
    (∑ q ∈ Q, sixVertexBetheTupleWaveWeight N c p
        (sixVertexSectorIntCoordinates x) q) =
      ∑ q ∈ Q, ∑ sigma : Equiv.Perm (Fin (n + 1)),
        sixVertexBetheAmplitude c p sigma *
          sixVertexBetheIntervalTupleWeight N c
            (fun i => sixVertexBethePhase (p (sigma i)))
            (sixVertexSectorIntCoordinates x) q := by
      apply Finset.sum_congr rfl
      intro q hq
      symm
      rw [show (∑ sigma : Equiv.Perm (Fin (n + 1)),
          sixVertexBetheAmplitude c p sigma *
            sixVertexBetheIntervalTupleWeight N c
              (fun i => sixVertexBethePhase (p (sigma i)))
              (sixVertexSectorIntCoordinates x) q) =
          sixVertexBetheTupleBoltzmann N c
              (sixVertexSectorIntCoordinates x) q *
            ∑ sigma, sixVertexBetheAmplitude c p sigma *
              sixVertexBetheIntMonomial p sigma q by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro sigma _
        rw [sixVertexBetheIntervalTupleWeight_factor]
        unfold sixVertexBetheTupleBoltzmann sixVertexBetheIntMonomial
        ring]
      rfl
    _ = ∑ sigma : Equiv.Perm (Fin (n + 1)),
        sixVertexBetheAmplitude c p sigma *
          sixVertexBetheCollisionFreeIntervalSum N c
            (fun i => sixVertexBethePhase (p (sigma i)))
            (sixVertexSectorIntCoordinates x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro sigma _
      unfold sixVertexBetheCollisionFreeIntervalSum
      dsimp only [Q, sixVertexBetheCollisionFreeTuples]
      rw [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro sigma _
      rw [sixVertexBetheCollisionFreeIntervalSum_zeroPhase N c
        (fun i => p (sigma i)) (sixVertexSectorIntCoordinates x)
        (sigma.symm ell)]
      · simp [hell]
      · exact sixVertexBetheShiftCoordinates_lt_sector x


end
end StatMech.FrontierD

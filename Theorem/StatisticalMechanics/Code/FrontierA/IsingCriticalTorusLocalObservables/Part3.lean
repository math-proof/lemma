/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalObservables.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusLocalLimit.Part2
import Theorem.StatisticalMechanics.Code.Probability.KKLfromHC.Part5
import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundaryDerivative
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part4
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusLocalObservables.Part3
open Filter Finset MeasureTheory Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Sharpness StatMech.FrontierB StatMech.Probability

noncomputable section

variable {d : Nat}


theorem finiteIsingWeightedSpinReal_compactTorusWeight
    (A : Finset (Site d)) (a : Site d → Real) (n : Nat)
    (sigma : ConfigSpace (IsingDyadicTorus d n)) :
    finiteIsingWeightedSpinReal (compactTorusWeight A a n) sigma =
      compactWeightedSpin A a (criticalTorusLocalRestriction A n sigma) := by
  unfold finiteIsingWeightedSpinReal compactTorusWeight compactWeightedSpin
    criticalTorusLocalRestriction
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_eq_single (isingSiteToDyadicTorus n x.1)]
  · simp only [if_pos rfl]
    congr 1
  · intro z hz hne
    simp [hne.symm]
  · simp

theorem finiteIsingWeightedRawMoment_eq_expJ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (a : V → Real) (order : Nat) :
    finiteIsingWeightedRawMoment G beta a order =
      expJ G.edgeFinset (fun _ ↦ beta) (fun _ ↦ 0)
        (fun sigma ↦ finiteIsingWeightedSpinReal a sigma ^ order) := by
  have hweight (sigma : ConfigSpace V) :
      zeroFieldInteractionWeight G beta sigma =
        wJ G.edgeFinset (fun _ ↦ beta) (fun _ ↦ 0) sigma := by
    unfold zeroFieldInteractionWeight wJ
    simp only [zero_mul, Finset.sum_const_zero, add_zero, Finset.mul_sum]
  unfold finiteIsingWeightedRawMoment expJ ZJ
  simp_rw [hweight]
  congr 1
  apply Finset.sum_congr rfl
  intro sigma hsigma
  ring


theorem criticalTorusCompactWeightedMoment_eq_finiteRawMoment
    (A : Finset (Site d)) (a : Site d → Real) (n order : Nat) :
    criticalTorusLocalObservableExpectation A
        (fun sigma ↦ compactWeightedSpin A a sigma ^ order) n =
      finiteIsingWeightedRawMoment (isingTorusGraph d n)
        (IsingFK.betaC (magnetization d)) (compactTorusWeight A a n) order := by
  rw [finiteIsingWeightedRawMoment_eq_expJ]
  unfold criticalTorusLocalObservableExpectation
  congr 1
  funext sigma
  rw [finiteIsingWeightedSpinReal_compactTorusWeight]


theorem scalarCumulantsOfMoments_tendsto_of_moments
    (moments : Nat → Nat → Real) (limitMoments : Nat → Real)
    (hmoments : ∀ order,
      Tendsto (fun n ↦ moments n order) atTop (nhds (limitMoments order))) :
    ∀ order, Tendsto
      (fun n ↦ scalarCumulantsOfMoments (moments n) order) atTop
      (nhds (scalarCumulantsOfMoments limitMoments order)) := by
  intro order
  induction order using Nat.strong_induction_on with
  | h order ih =>
      cases order with
      | zero => simp
      | succ order =>
          rw [show order + 1 = order + 1 by rfl,
            scalarCumulantsOfMoments_succ]
          have hsum : Tendsto
              (fun n ↦ ∑ k : Fin order,
                (order.choose k : Real) *
                  scalarCumulantsOfMoments (moments n) (k + 1) *
                    moments n (order - k))
              atTop
              (nhds (∑ k : Fin order,
                (order.choose k : Real) *
                  scalarCumulantsOfMoments limitMoments (k + 1) *
                    limitMoments (order - k))) := by
            apply tendsto_finsetSum
            intro k hk
            exact (tendsto_const_nhds.mul (ih (k + 1) (by omega))).mul
              (hmoments (order - k))
          have h := (hmoments (order + 1)).sub hsum
          convert h using 1
          funext n
          rw [scalarCumulantsOfMoments_succ]


end
end StatMech.FrontierA

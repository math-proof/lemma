/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalFreeBoxLocalObservables.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusLocalObservables.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.ScalarCumulantsContinuity
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalFreeBoxLocalObservables.Part2
open Filter Finset MeasureTheory Topology
open scoped BigOperators


namespace StatMech.FrontierA

open ProbabilityTheory StatMech Ising Lattice Sharpness StatMech.FrontierB
  StatMech.Probability

noncomputable section

variable {d : Nat}

theorem finiteIsingWeightedSpinReal_compactFreeBoxWeight
    (A : Finset (Site d)) (a : Site d → Real) (n : Nat)
    (hA : (↑A : Set (Site d)) ⊆ box d n)
    (tau : ConfigSpace (sctBox d n)) :
    finiteIsingWeightedSpinReal (compactFreeBoxWeight A a n) tau =
      compactWeightedSpin A a
        (criticalInfiniteLocalRestriction A (glue (minusField d) tau)) := by
  unfold finiteIsingWeightedSpinReal compactFreeBoxWeight compactWeightedSpin
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  change (∑ x ∈ boxSpinSupport d n A, a x.1 * spin tau x) = _
  apply Finset.sum_bij
      (fun x hx ↦ ⟨x.1, by simpa [boxSpinSupport] using hx⟩)
  · intro x hx
    simp
  · intro x hx y hy hxy
    apply Subtype.ext
    exact congrArg (fun z : {z // z ∈ A} ↦ z.1) hxy
  · intro y hy
    let x : sctBox d n := ⟨y.1, hA y.2⟩
    refine ⟨x, ?_, ?_⟩
    · simp [x, boxSpinSupport, y.2]
    · apply Subtype.ext
      rfl
  · intro x hx
    congr 1
    change spin tau x = spin (glue (minusField d) tau) x.1
    unfold spin
    rw [glue_mem (minusField d) tau (hA (by simpa [boxSpinSupport] using hx))]

theorem finiteIsingWeightedRawMoment_eq_isingExpectation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (a : V → Real) (order : Nat) :
    finiteIsingWeightedRawMoment G beta a order =
      isingExpectation G beta 0
        (fun sigma ↦ finiteIsingWeightedSpinReal a sigma ^ order) := by
  have hweight (sigma : ConfigSpace V) :
      zeroFieldInteractionWeight G beta sigma =
        isingWeight G beta 0 sigma := by
    unfold zeroFieldInteractionWeight isingWeight hamiltonian
    congr 1
    simp
  unfold finiteIsingWeightedRawMoment isingExpectation isingProb isingZ
  simp_rw [← hweight, div_mul_eq_mul_div]
  rw [Finset.sum_div]


theorem criticalFreeBoxCompactWeightedMoment_eq_finiteRawMoment
    (A : Finset (Site d)) (a : Site d → Real) (n order : Nat)
    (hA : (↑A : Set (Site d)) ⊆ box d n) :
    criticalFreeBoxCompactWeightedMoment A a n order =
      finiteIsingWeightedRawMoment (sctBoxGraph d n)
        (IsingFK.betaC (magnetization d))
        (compactFreeBoxWeight A a n) order := by
  unfold criticalFreeBoxCompactWeightedMoment
    criticalFreeBoxLocalObservableExpectation
  change (∫ omega,
      compactWeightedSpin A a
          (criticalInfiniteLocalRestriction A omega) ^ order
        ∂(fvMeasure (minusField d) n (bondFinsetInternal d n)
          (IsingFK.betaC (magnetization d)) 0)) = _
  rw [integral_fvMeasure_eq_sum,
    finiteIsingWeightedRawMoment_eq_isingExpectation]
  unfold isingExpectation
  apply Finset.sum_congr rfl
  intro tau htau
  rw [sct_fvProb_eq_isingProb]
  congr 1
  change compactWeightedSpin A a
      (criticalInfiniteLocalRestriction A (glue (minusField d) tau)) ^ order =
    finiteIsingWeightedSpinReal (compactFreeBoxWeight A a n) tau ^ order
  rw [finiteIsingWeightedSpinReal_compactFreeBoxWeight A a n hA tau]


theorem criticalFreeBoxCompactWeightedCumulant_eq_finiteCumulant
    (A : Finset (Site d)) (a : Site d → Real) (n order : Nat)
    (hA : (↑A : Set (Site d)) ⊆ box d n) :
    criticalFreeBoxCompactWeightedCumulant A a n order =
      PhysicalIsing.finiteIsingWeightedCumulant (sctBoxGraph d n)
        (IsingFK.betaC (magnetization d))
        (compactFreeBoxWeight A a n) order := by
  unfold criticalFreeBoxCompactWeightedCumulant
    PhysicalIsing.finiteIsingWeightedCumulant
  congr 1
  funext m
  exact criticalFreeBoxCompactWeightedMoment_eq_finiteRawMoment A a n m hA

theorem criticalFreeBoxCompactWeightedMoment_tendsto
    (hd : 2 < d) (A : Finset (Site d)) (a : Site d → Real) (order : Nat) :
    Tendsto (fun n ↦ criticalFreeBoxCompactWeightedMoment A a n order)
      atTop
      (nhds (criticalFreeLocalObservableExpectation A
        (fun sigma ↦ compactWeightedSpin A a sigma ^ order))) := by
  exact criticalFreeBoxLocalObservableExpectation_tendsto hd A _


theorem criticalFreeBoxCompactWeightedCumulant_tendsto
    (hd : 2 < d) (A : Finset (Site d)) (a : Site d → Real) (order : Nat) :
    Tendsto (fun n ↦ criticalFreeBoxCompactWeightedCumulant A a n order)
      atTop (nhds (criticalFreeCompactWeightedCumulant A a order)) := by
  unfold criticalFreeBoxCompactWeightedCumulant
    criticalFreeCompactWeightedCumulant
  apply tendsto_scalarCumulantsOfMoments
  intro m
  exact criticalFreeBoxCompactWeightedMoment_tendsto hd A a m

end
end StatMech.FrontierA

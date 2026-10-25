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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalFreeBoxLocalObservables
open Filter Finset MeasureTheory Topology
open scoped BigOperators


namespace StatMech.FrontierA

open ProbabilityTheory StatMech Ising Lattice Sharpness StatMech.FrontierB
  StatMech.Probability

noncomputable section

variable {d : Nat}

set_option maxHeartbeats 800000 in


theorem criticalFreeBoxLocalObservableExpectation_tendsto
    (hd : 2 < d) (A : Finset (Site d))
    (f : ConfigSpace {x // x ∈ A} → Real) :
    Tendsto (fun n ↦ criticalFreeBoxLocalObservableExpectation A f n)
      atTop (nhds (criticalFreeLocalObservableExpectation A f)) := by
  let c : Finset {x // x ∈ A} → Real := fun B ↦
    khc_fourierCoeff f B * (-1 : Real) ^ B.card
  have hbox (n : Nat) :
      criticalFreeBoxLocalObservableExpectation A f n =
        ∑ B : Finset {x // x ∈ A}, c B *
          ∫ omega,
            spinProd (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) omega
              ∂(freeMeasure d n (IsingFK.betaC (magnetization d)) 0 :
                Measure (ConfigSpace (Site d))) := by
    unfold criticalFreeBoxLocalObservableExpectation
    have hpoint (omega : ConfigSpace (Site d)) :
        f (criticalInfiniteLocalRestriction A omega) =
          ∑ B : Finset {x // x ∈ A}, c B *
            spinProd
              (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) omega := by
      rw [← khc_fourier_expansion f (criticalInfiniteLocalRestriction A omega)]
      apply Finset.sum_congr rfl
      intro B _
      rw [freeBox_walshChar_infiniteRestriction A B omega]
      dsimp [c]
      ring
    simp_rw [hpoint]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro B hB
      rw [integral_const_mul]
    · intro B hB
      exact ((spinProdBCF d
        (B.map (Function.Embedding.subtype fun x ↦ x ∈ A))).integrable _).const_mul
          (c B)
  have hsum : Tendsto
      (fun n ↦ ∑ B : Finset {x // x ∈ A}, c B *
        ∫ omega,
          spinProd (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) omega
            ∂(freeMeasure d n (IsingFK.betaC (magnetization d)) 0 :
              Measure (ConfigSpace (Site d))))
      atTop
      (nhds (∑ B : Finset {x // x ∈ A}, c B *
        ∫ omega,
          spinProd (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) omega
            ∂(freeState d (IsingFK.betaC (magnetization d)) 0 :
              Measure (ConfigSpace (Site d))))) := by
    apply tendsto_finsetSum
    intro B hB
    apply Tendsto.const_mul
    exact integral_freeMeasure_spinProd_tendsto_freeState d
      (IsingFK.betaC (magnetization d))
      (by
        rw [isingFK_betaC_eq_tildeBetaCIsing (by omega : 2 ≤ d)]
        exact (tildeBetaCIsing_pos (by omega)).le)
      (B.map (Function.Embedding.subtype fun x ↦ x ∈ A))
  have hlimit :
      (∑ B : Finset {x // x ∈ A}, c B *
        ∫ omega,
          spinProd (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) omega
            ∂(freeState d (IsingFK.betaC (magnetization d)) 0 :
              Measure (ConfigSpace (Site d)))) =
        criticalFreeLocalObservableExpectation A f := by
    unfold criticalFreeLocalObservableExpectation
    have hpoint (omega : ConfigSpace (Site d)) :
        f (criticalInfiniteLocalRestriction A omega) =
          ∑ B : Finset {x // x ∈ A}, c B *
            spinProd
              (B.map (Function.Embedding.subtype fun x ↦ x ∈ A)) omega := by
      rw [← khc_fourier_expansion f (criticalInfiniteLocalRestriction A omega)]
      apply Finset.sum_congr rfl
      intro B _
      rw [freeBox_walshChar_infiniteRestriction A B omega]
      dsimp [c]
      ring
    simp_rw [hpoint]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro B hB
      rw [integral_const_mul]
    · intro B hB
      exact ((spinProdBCF d
        (B.map (Function.Embedding.subtype fun x ↦ x ∈ A))).integrable _).const_mul
          (c B)
  rw [← hlimit]
  exact hsum.congr' (Filter.Eventually.of_forall fun n ↦ (hbox n).symm)


end
end StatMech.FrontierA

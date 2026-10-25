/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalCumulants.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedMomentBridge.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part4
open Filter Finset Topology
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

namespace PhysicalIsing

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem exists_criticalFiniteBoxWeightedNormalizedFourthCumulant_eq_scaled
    (d n : Nat) (hd : 2 <= d) (a : sctBox d n -> Real) :
    ∃ c : Real, 0 < c ∧
      criticalFiniteBoxWeightedNormalizedFourthCumulant d n a =
        scalarCumulantsOfMoments
          (fun order => c ^ order *
            finiteIsingWeightedRawMoment
              (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) a order) 4 := by
  obtain ⟨c, hc, hpow⟩ := exists_criticalFiniteBoxWeightedFourthScale d n hd
  exact ⟨c, hc,
    criticalFiniteBoxWeightedNormalizedFourthCumulant_eq_scaled
      d n a c hpow⟩


theorem criticalFiniteBoxWeightedScaledFourthCumulant_tendsto_zero
    (d : Nat) (hd : 4 < d)
    (a : (n : Nat) -> sctBox d n -> Real)
    (ha0 : forall n i, 0 <= a n i)
    (ha1 : forall n i, a n i <= 1) :
    Tendsto
      (fun n => scalarCumulantsOfMoments
        (fun order =>
          criticalFiniteBoxWeightedFourthScale d n (by omega) ^ order *
            finiteIsingWeightedRawMoment
              (sctBoxGraph d n) (IsingFK.betaC (magnetization d))
                (a n) order) 4)
      atTop (nhds 0) := by
  have h := criticalFiniteBoxWeightedNormalizedFourthCumulant_tendsto_zero
    d hd a ha0 ha1
  convert h using 1
  funext n
  exact (criticalFiniteBoxWeightedNormalizedFourthCumulant_eq_scaled
    d n (a n) (criticalFiniteBoxWeightedFourthScale d n (by omega))
    (criticalFiniteBoxWeightedFourthScale_pow_four d n (by omega))).symm

theorem criticalFiniteBoxWeightedScaledCumulant_four_tendsto_zero
    (d : Nat) (hd : 4 < d)
    (a : (n : Nat) -> sctBox d n -> Real)
    (ha0 : forall n i, 0 <= a n i)
    (ha1 : forall n i, a n i <= 1) :
    Tendsto
      (fun n => criticalFiniteBoxWeightedScaledCumulant
        d n (by omega) (a n) 4) atTop (nhds 0) := by
  simpa [criticalFiniteBoxWeightedScaledCumulant] using
    criticalFiniteBoxWeightedScaledFourthCumulant_tendsto_zero
      d hd a ha0 ha1

end PhysicalIsing
end
end StatMech.FrontierA

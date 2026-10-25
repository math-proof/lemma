/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusCumulants.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianTorusScalingHandoff
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part19
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardCumulants.Part3
open Filter MeasureTheory Topology
open scoped BigOperators


namespace StatMech.FrontierA

open ProbabilityTheory StatMech Ising StatMech.FrontierB

noncomputable section

variable {d k : Nat}


theorem isingTorusZeroFieldMass_eq_finiteIsingWeight
    (beta : Real) (sigma : ConfigSpace (IsingDyadicTorus d k)) :
    isingTorusZeroFieldMass beta sigma =
      zeroFieldInteractionWeight (isingTorusGraph d k) beta sigma /
        ∑ tau : ConfigSpace (IsingDyadicTorus d k),
          zeroFieldInteractionWeight (isingTorusGraph d k) beta tau := by
  unfold isingTorusZeroFieldMass
  rw [isingTorus_zero_weight_eq_graph_weight,
    isingTorusShiftedPartition_zero_eq_graph]
  have hscale : Real.exp (-beta *
      (Fintype.card (IsingDyadicTorus d k) : Real) * d) ≠ 0 :=
    (Real.exp_pos _).ne'
  rw [mul_div_mul_left _ _ hscale]
  unfold isingZ isingWeight hamiltonian zeroFieldInteractionWeight
  simp only [zero_mul, sub_zero]
  congr 1
  · congr 1
    ring
  · apply Finset.sum_congr rfl
    intro tau _
    congr 1
    ring


theorem integral_pow_isingTorusSmearedSpin_eq_finiteIsingWeightedRawMoment
    (beta : Real) (a : IsingDyadicTorus d k → Real) (order : Nat) :
    (∫ sigma, isingTorusSmearedSpin a sigma ^ order
        ∂(isingTorusZeroFieldLaw (d := d) (k := k) beta :
          ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k)))) =
      finiteIsingWeightedRawMoment
        (isingTorusGraph d k) beta a order := by
  rw [integral_isingTorusZeroFieldLaw]
  unfold finiteIsingWeightedRawMoment
  simp_rw [isingTorusZeroFieldMass_eq_finiteIsingWeight]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro sigma _
  have hspin : isingTorusSmearedSpin a sigma =
      finiteIsingWeightedSpinReal a sigma := by
    unfold isingTorusSmearedSpin finiteIsingWeightedSpinReal
      isingTorusSpinField
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hspin]
  ring


end
end StatMech.FrontierA

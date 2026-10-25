/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge.Part5
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectShiftedEndpoint.Part3
import Def.StatisticalMechanics.Code.Onsager.SignedLoopHighTempResummation.Part2
open scoped BigOperators
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Ising StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem kwEvenPolynomial_setEdge_affine
    (weight : Sym2 V → Complex) (edge : Sym2 V) (z : Complex) :
    kwEvenPolynomial G (ons_setGraphEdgeWeight weight edge z) =
      kwEvenPolynomial G (ons_setGraphEdgeWeight weight edge 0) +
        z * ons_kwEvenEdgeCoefficient G weight edge := by
  classical
  unfold kwEvenPolynomial ons_kwEvenEdgeCoefficient
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro F hF
  by_cases hedge : edge ∈ F
  · rw [prod_ons_setGraphEdgeWeight_of_mem weight edge z F hedge,
      prod_ons_setGraphEdgeWeight_of_mem weight edge 0 F hedge]
    simp [hedge]
  · rw [prod_ons_setGraphEdgeWeight_of_not_mem weight edge z F hedge,
      prod_ons_setGraphEdgeWeight_of_not_mem weight edge 0 F hedge]
    simp [hedge]


end
end StatMech.Onsager

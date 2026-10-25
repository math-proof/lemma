/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectCutCycle.Part12
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCutLimit
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge.Part5
import Def.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectKacWard.Part2
open scoped BigOperators
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA

noncomputable section

theorem ofReal_ons_plusRectContourSum_eq_kwEvenPolynomial
    (n : Nat) (q : Real) :
    (ons_plusRectContourSum n q : Complex) =
      kwEvenPolynomial (ons_rectDualGraph (2 * n + 1) (2 * n + 1))
        (fun _ => (q : Complex)) := by
  rw [kwEvenPolynomial_eq_sum_actual]
  unfold ons_plusRectContourSum
  push_cast
  apply Finset.sum_congr rfl
  intro F _
  simp [Finset.prod_const]


theorem ofReal_ons_plusRectPathSum_eq_kwEvenPolynomial
    (n : Nat) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v) (q : Real) :
    (ons_plusRectPathSum n path q : Complex) =
      kwEvenPolynomial (ons_rectDualGraph (2 * n + 1) (2 * n + 1))
        (ons_plusRectPathWeight n path q) := by
  rw [kwEvenPolynomial_eq_sum_actual]
  unfold ons_plusRectPathSum
  push_cast
  apply Finset.sum_congr rfl
  intro F _
  unfold ons_plusRectPathDefectSign ons_plusRectPathWeight
  rw [Finset.prod_mul_distrib]
  push_cast
  simp [Finset.prod_const]


end
end StatMech.Onsager

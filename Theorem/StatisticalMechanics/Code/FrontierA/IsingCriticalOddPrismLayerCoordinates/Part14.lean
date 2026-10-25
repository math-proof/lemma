/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3
import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part14


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem sum_transferTailPathWeight_mul_endpoint
    {E : Type*} [Fintype E] [DecidableEq E]
    (A : Matrix E E Real) (hA : A.IsHermitian)
    (a f : E -> Real) (k : Nat) :
    (∑ q : Fin (k + 1) -> E,
      transferTailPathWeight A a k q * f (q (Fin.last k))) =
      ∑ s, ((A ^ k) *ᵥ a) s * f s := by
  have hpath := dot_mulVec_pow_eq_sum_path A a f k
  unfold transferTailPathWeight
  rw [← hpath]
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [show (∑ x, a x * ((A ^ k) x s * f s)) =
      (∑ x, (A ^ k) s x * a x) * f s by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    have hs := (hA.pow k).apply s x
    simp only [star_trivial] at hs
    rw [hs]
    ring]


end
end StatMech.FrontierA

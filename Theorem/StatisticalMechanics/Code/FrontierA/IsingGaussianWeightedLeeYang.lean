/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedLeeYang.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part15
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedLeeYang
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem leeYangWeightedDiagonal_norm_lt
    (a : V -> Real) (ha : forall v, 0 < a v)
    {z : Complex} (hz : 0 < z.re) :
    forall k, ‖leeYangWeightedDiagonal G a z k‖ < 1 := by
  intro k
  rcases k with v | ⟨v, e⟩
  · unfold leeYangWeightedDiagonal
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    norm_num [Complex.mul_re]
    nlinarith [ha v]
  · simp [leeYangWeightedDiagonal]


theorem leeYangContractedProduct_weighted_ne_zero
    {beta : Real} (hbeta : 0 <= beta)
    (a : V -> Real) (ha : forall v, 0 < a v)
    {z : Complex} (hz : 0 < z.re) :
    leeYangContractedProduct G beta (leeYangWeightedDiagonal G a z) ≠ 0 := by
  apply leeYangContractedProduct_stable G hbeta
  exact leeYangWeightedDiagonal_norm_lt G a ha hz


end
end StatMech.FrontierA

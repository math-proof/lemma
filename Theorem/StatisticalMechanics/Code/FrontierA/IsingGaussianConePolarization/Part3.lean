/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianConePolarization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanBridge.Part2
import Mathlib.LinearAlgebra.Lagrange
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization.Part2
open Filter Finset Polynomial Topology


namespace StatMech.FrontierA

theorem smearingStrictPositivePart_pos
    {V : Type*} [Fintype V] (a : V -> Real) (v : V) :
    0 < smearingStrictPositivePart a v := by
  classical
  have hv : |a v| <= ∑ w : V, |a w| :=
    Finset.single_le_sum (fun w _ => abs_nonneg (a w)) (Finset.mem_univ v)
  have hneg : -|a v| <= a v := neg_abs_le (a v)
  unfold smearingStrictPositivePart smearingStrictShift
  linarith

theorem smearingStrictNegativePart_pos
    {V : Type*} [Fintype V] (a : V -> Real) (v : V) :
    0 < smearingStrictNegativePart a v := by
  classical
  unfold smearingStrictNegativePart smearingStrictShift
  have hsum : 0 <= ∑ w : V, |a w| :=
    Finset.sum_nonneg fun w _ => abs_nonneg (a w)
  linarith

theorem smearing_eq_strictPositivePart_sub_strictNegativePart
    {V : Type*} [Fintype V] (a : V -> Real) :
    a = smearingStrictPositivePart a - smearingStrictNegativePart a := by
  funext v
  simp [smearingStrictPositivePart, smearingStrictNegativePart]


end StatMech.FrontierA

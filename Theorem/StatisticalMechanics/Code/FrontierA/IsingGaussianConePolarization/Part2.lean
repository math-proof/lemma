/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianConePolarization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanBridge.Part2
import Mathlib.LinearAlgebra.Lagrange
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization
open Filter Finset Polynomial Topology


namespace StatMech.FrontierA

theorem smearingPositivePart_nonneg {V : Type*} (a : V -> Real) (v : V) :
    0 <= smearingPositivePart a v := by
  simp [smearingPositivePart]

theorem smearingNegativePart_nonneg {V : Type*} (a : V -> Real) (v : V) :
    0 <= smearingNegativePart a v := by
  simp [smearingNegativePart]

theorem smearing_eq_positivePart_sub_negativePart
    {V : Type*} (a : V -> Real) :
    a = smearingPositivePart a - smearingNegativePart a := by
  funext v
  exact (max_zero_sub_max_neg_zero_eq_self (a v)).symm


end StatMech.FrontierA

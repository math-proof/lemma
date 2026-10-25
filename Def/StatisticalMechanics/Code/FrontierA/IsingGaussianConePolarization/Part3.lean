/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianConePolarization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanBridge.Part2
import Mathlib.LinearAlgebra.Lagrange
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization.Part3
open Filter Finset Polynomial Topology


namespace StatMech.FrontierA

noncomputable def finiteWeightedCumulant
    {V : Type*} [Fintype V] (order : Nat)
    (ursell : (Fin order -> V) -> Real) (a : V -> Real) : Real :=
  ∑ x : Fin order -> V, ursell x * ∏ i : Fin order, a (x i)


noncomputable def finiteWeightedCumulantLinePolynomial
    {V : Type*} [Fintype V] (order : Nat)
    (ursell : (Fin order -> V) -> Real)
    (positive negative : V -> Real) : Real[X] :=
  ∑ x : Fin order -> V, C (ursell x) *
    ∏ i : Fin order, (C (positive (x i)) + C (negative (x i)) * X)

end StatMech.FrontierA

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianConePolarization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanBridge.Part2
import Mathlib.LinearAlgebra.Lagrange
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization.Part2
open Filter Finset Polynomial Topology


namespace StatMech.FrontierA

noncomputable def smearingStrictShift
    {V : Type*} [Fintype V] (a : V -> Real) : Real :=
  1 + ∑ v : V, |a v|

noncomputable def smearingStrictPositivePart
    {V : Type*} [Fintype V] (a : V -> Real) : V -> Real :=
  fun v => a v + smearingStrictShift a

noncomputable def smearingStrictNegativePart
    {V : Type*} [Fintype V] (a : V -> Real) : V -> Real :=
  fun _ => smearingStrictShift a

end StatMech.FrontierA

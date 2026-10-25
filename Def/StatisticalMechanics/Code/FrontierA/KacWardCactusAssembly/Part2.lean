/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCactusAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnicyclicAssembly.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardCactusAssembly
open scoped BigOperators


namespace StatMech.FrontierA

open Matrix


noncomputable def kwAbstractCactusEvenPolynomial
    {E Block : Type*} [Fintype E] [Fintype Block]
    (edgeWeight : Block -> E -> ℂ) : ℂ :=
  ∏ b, kwAbstractCycleEvenPolynomial (edgeWeight b)


end StatMech.FrontierA

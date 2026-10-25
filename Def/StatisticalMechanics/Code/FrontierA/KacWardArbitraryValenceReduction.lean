/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardArbitraryValenceReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainEvenPolynomial.Part11
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part6


namespace StatMech.FrontierA

open SimpleGraph

open Finset Polynomial

open StatMech.Onsager

open scoped BigOperators


noncomputable def kwDetOneSubWith
    {D : Type*} [Fintype D] (decEq : DecidableEq D)
    (M : Matrix D D Complex) : Complex :=
  @Matrix.det D decEq _ Complex _
    ((@Matrix.one D Complex decEq _ _).one - M)

end StatMech.FrontierA

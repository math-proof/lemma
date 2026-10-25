/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part12
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnitCycleReduction
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part4
open scoped BigOperators
open Finset SimpleGraph Polynomial


namespace StatMech.FrontierA

open StatMech.Onsager

open StatMech.Ising

universe u


noncomputable def kwDetScalePolynomial
    {E : Type*} [Fintype E] [DecidableEq E]
    (M : Matrix E E ℂ) : ℂ[X] :=
  ((1 : Matrix E E ℂ[X]) -
    Matrix.of (fun i j : E ↦ X * C (M i j))).det

end StatMech.FrontierA

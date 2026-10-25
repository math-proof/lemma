/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part12
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnitCycleReduction
import Def.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part4
open scoped BigOperators
open Finset SimpleGraph Polynomial


namespace StatMech.FrontierA

open StatMech.Onsager

open StatMech.Ising

universe u


theorem kwDetScalePolynomial_eval
    {E : Type*} [Fintype E] [DecidableEq E]
    (M : Matrix E E ℂ) (t : ℂ) :
    (kwDetScalePolynomial M).eval t = (1 - t • M).det := by
  rw [kwDetScalePolynomial, ← Polynomial.coe_evalRingHom,
    RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [smul_eq_mul, h] <;> ring


end StatMech.FrontierA

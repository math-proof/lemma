/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIncidentStairPatch.Part2


namespace StatMech.FrontierA

open scoped NNReal

open Set


structure KWStairParameterData
    {n S : ℕ} [NeZero n] [NeZero S]
    (polygon : KWFiniteSimplePolygon n) where
  parameter : Fin n → Fin (S + 1) → ℝ
  parameter_zero : ∀ i, parameter i 0 = 0
  parameter_last : ∀ i, parameter i (Fin.last S) = 1
  parameter_strict : ∀ i (k : Fin S),
    parameter i k.castSucc < parameter i k.succ


end StatMech.FrontierA

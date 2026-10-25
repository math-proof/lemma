/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisWord.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalNormalization.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisWord.Part2


namespace StatMech.FrontierA

open StatMech.Onsager.BaseCase


def kwIntegralPolygonDirection
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ)
    (k : Fin (kwIntegralPolygonWord p).length) : Fin 4 :=
  (kwIntegralPolygonWord p).get k


end StatMech.FrontierA

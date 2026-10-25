/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisWord.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalNormalization.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisWord


namespace StatMech.FrontierA

open StatMech.Onsager.BaseCase


def kwIntegralPolygonEdgeWord {n : ℕ} [NeZero n]
    (p : Fin n → ℤ × ℤ) (i : Fin n) : List (Fin 4) :=
  kwIntegralAxisWord (p (i + 1) - p i)


def kwIntegralPolygonWord {n : ℕ} [NeZero n]
    (p : Fin n → ℤ × ℤ) : List (Fin 4) :=
  (List.ofFn (kwIntegralPolygonEdgeWord p)).flatten

end StatMech.FrontierA

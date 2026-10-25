/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisWord.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalNormalization.Part3


namespace StatMech.FrontierA

open StatMech.Onsager.BaseCase


def kwHorizontalIntDirection (x : ℤ) : Fin 4 :=
  if 0 ≤ x then 0 else 2


def kwVerticalIntDirection (y : ℤ) : Fin 4 :=
  if 0 ≤ y then 1 else 3


def kwIntegralAxisWord (v : ℤ × ℤ) : List (Fin 4) :=
  List.replicate v.1.natAbs (kwHorizontalIntDirection v.1) ++
    List.replicate v.2.natAbs (kwVerticalIntDirection v.2)

end StatMech.FrontierA

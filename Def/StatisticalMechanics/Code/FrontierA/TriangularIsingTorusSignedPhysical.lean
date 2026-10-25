/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhysical.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part6
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


def triangularTorusLinearCharacter
    (chi h : Fin 2 × Fin 2) : Real :=
  (-1 : Real) ^ (chi.1.val * h.1.val + chi.2.val * h.2.val)


def triangularTorusQuadraticWalshSign
    (a b : Fin 2) (chi : Fin 2 × Fin 2) : Real :=
  (-1 : Real) ^
    ((1 + a.val + chi.1.val) * (1 + b.val + chi.2.val))


end StatMech.FrontierA

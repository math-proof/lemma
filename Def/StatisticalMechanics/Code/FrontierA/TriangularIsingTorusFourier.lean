/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusKacWard.Part2
import Theorem.StatisticalMechanics.Code.Onsager.KWSpinFourier.Part3
import Abbrev.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFourier
open scoped BigOperators Matrix


namespace StatMech.FrontierA

open StatMech.Onsager

def triangularTorusDirectionStep (L : Nat) : Fin 6 → ZMod L × ZMod L :=
  ![(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)]

def triangularTorusDirectionWeight
    (t1 t2 t3 : Complex) : Fin 6 -> Complex :=
  ![t1, t1, t2, t2, t3, t3]

noncomputable def triangularTorusDirectionPhase
    (u v : Complex) : Fin 6 -> Complex :=
  ![u, u⁻¹, v, v⁻¹, u * v, (u * v) ⁻¹]


noncomputable def triangularTorusKWBlock
    (L : Nat) (t1 t2 t3 rho u v : Complex)
    (g : ZMod L × ZMod L) : Matrix (Fin 6) (Fin 6) Complex :=
  fun a b =>
    if g = triangularTorusDirectionStep L a then
      triangularTorusDirectionPhase u v a *
        triangularTorusDirectionWeight t1 t2 t3 a *
          triangularKacWardTurnMatrix rho a b
    else 0


noncomputable def triangularTorusKWMatrix
    (L : Nat) (t1 t2 t3 rho u v : Complex) :
    Matrix (triangularTorusDart L) (triangularTorusDart L) Complex :=
  ons_blockCirculant2D L 6
    (triangularTorusKWBlock L t1 t2 t3 rho u v)

end StatMech.FrontierA

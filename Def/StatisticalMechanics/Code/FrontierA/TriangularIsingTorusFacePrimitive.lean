/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFacePotential.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhaseAssembly
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFacePrimitive
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

def triangularTorusPositiveIndex : Fin 6 → Fin 3 := ![0, 0, 1, 1, 2, 2]

def triangularTorusPositiveSource {L : Nat}
    (d : triangularTorusDart L) : ZMod L × ZMod L :=
  match d.2.val with
  | 0 => (d.1.1 - 1, d.1.2)
  | 1 => d.1
  | 2 => (d.1.1, d.1.2 - 1)
  | 3 => d.1
  | 4 => (d.1.1 - 1, d.1.2 - 1)
  | _ => d.1

def triangularFacePositiveCoeff {L : Nat}
    (lower upper : (ZMod L × ZMod L) → ZMod 2)
    (a : Fin 3) (p : ZMod L × ZMod L) : Int :=
  match a.val with
  | 0 => triangularFaceEastCoeff lower upper p
  | 1 => triangularFaceNorthCoeff lower upper p
  | _ => triangularFaceDiagonalCoeff lower upper p

def triangularTorusPositiveRepresentation {L : Nat}
    (d : triangularTorusDart L) : Fin 3 × (ZMod L × ZMod L) :=
  (triangularTorusPositiveIndex d.2, triangularTorusPositiveSource d)

end StatMech.FrontierA

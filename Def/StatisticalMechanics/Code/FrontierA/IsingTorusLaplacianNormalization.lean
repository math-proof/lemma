/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusLaplacianNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGraph.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusExponentialMoment
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusLaplacianNormalization
open Finset Matrix
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


def isingTorusIndexedDart
    (p : IsingDyadicTorus d k × Fin d) :
    (isingTorusGraph d k).Dart :=
  ⟨(p.1, p.1 + isingTorusStep p.2), ⟨p.2, Or.inl rfl⟩⟩


def isingTorusOrientedIndexedDart
    (p : (IsingDyadicTorus d k × Fin d) × Bool) :
    (isingTorusGraph d k).Dart :=
  if p.2 then (isingTorusIndexedDart p.1).symm
  else isingTorusIndexedDart p.1

end StatMech.FrontierA

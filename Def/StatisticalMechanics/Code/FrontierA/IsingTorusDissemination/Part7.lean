/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part10
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusCharacter.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusDissemination.Part6
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


def IsingTorusDisseminatedBox (s : Fin d → Nat)
    (h : IsingDyadicTorus d k → Real) : Prop :=
  ∀ x, (∀ i, (x i).val < s i) → h x = h 0

end StatMech.FrontierA

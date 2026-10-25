/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part10
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusCharacter.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusDissemination.Part2
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


theorem isingTorusShiftedPartition_polarization_at
    (i : Fin d) (a : IsingDyadicTorus d k)
    (beta : Real) (hbeta : 0 ≤ beta)
    (h : IsingDyadicTorus d k → Real) :
    2 * isingTorusShiftedPartition beta h ≤
      isingTorusShiftedPartition beta (isingTorusPolarizeLowerAt i a h) +
        isingTorusShiftedPartition beta (isingTorusPolarizeUpperAt i a h) := by
  unfold isingTorusPolarizeLowerAt isingTorusPolarizeUpperAt
  simpa only [isingTorusShiftedPartition_translateField] using
    (isingTorusShiftedPartition_polarization i beta hbeta
      (isingTorusTranslateField a h))


end StatMech.FrontierA

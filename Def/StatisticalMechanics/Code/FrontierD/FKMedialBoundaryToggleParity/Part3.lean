/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryToggleParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part2
open Equiv


namespace StatMech.FrontierD

variable {T : EvenTorus}


def fkMedialBlackDartSwap (v : T.Vertex) : Perm (FKMedialBlackDart T) :=
  Equiv.swap (fkMedialBlackDart0 v) (fkMedialBlackDart1 v)

end StatMech.FrontierD

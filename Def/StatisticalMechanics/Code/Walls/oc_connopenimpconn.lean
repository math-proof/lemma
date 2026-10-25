/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_connopenimpconn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.ReachBoxCrossing.Part2
import Theorem.StatisticalMechanics.Code.Walls.oc_connopenimpconn
open scoped BigOperators


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.RevealmentBoxCrossing

open StatMech.OSSS.ReachBoxCrossing

open StatMech.Lattice

set_option linter.unusedSectionVars false

set_option linter.style.longLine false

variable {E : Type*} [Fintype E] [DecidableEq E]


def oc_site0 : Site 1 := ![0]


def oc_site1 : Site 1 := ![1]


def oc_witnessEndU : Fin 1 → Site 1 := fun _ => oc_site0

def oc_witnessEndV : Fin 1 → Site 1 := fun _ => oc_site1


def oc_witnessEdge : Fin 1 → Sym2 (Site 1) := fun _ => s(oc_site0, oc_site1)


end Walls
end StatMech

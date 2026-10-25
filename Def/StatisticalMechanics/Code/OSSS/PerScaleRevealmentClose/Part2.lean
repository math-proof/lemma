/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PerScaleRevealmentClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.PrefixCoversClose.Part3
import Theorem.StatisticalMechanics.Code.OSSS.FKRevealmentClose
import Theorem.StatisticalMechanics.Code.OSSS.PerScaleRevealmentClose.Part2
open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace PerScaleRevealmentClose

open OSSS.Coding

open OSSS.AdaptMConditional

open StatMech.OSSS

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.ReachBoxCrossing

open StatMech.OSSS.ReachDomination

open StatMech.OSSS.RevealmentBoxCrossing

open StatMech.OSSS.PrefixCoversClose

open StatMech.OSSS.FKRevealmentClose

open StatMech.OSSS.MonotonicFK

open StatMech.Lattice

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {V : Type*} [DecidableEq V]


def psr_witnessEndU : Fin 3 → Fin 4 := ![1, 0, 2]


def psr_witnessEndV : Fin 3 → Fin 4 := ![2, 1, 3]


end PerScaleRevealmentClose
end OSSS
end StatMech

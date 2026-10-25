/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PrefixCoversClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.ReachDomination.Part3
import Theorem.StatisticalMechanics.Code.OSSS.PrefixCoversClose
open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace PrefixCoversClose

open OSSS.Coding

open StatMech.OSSS

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.ReachBoxCrossing

open StatMech.OSSS.ReachDomination

open StatMech.Lattice

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {V : Type*} [DecidableEq V]


def topCfg (E : Type*) : ConfigSpace E := fun _ => true

end PrefixCoversClose
end OSSS
end StatMech

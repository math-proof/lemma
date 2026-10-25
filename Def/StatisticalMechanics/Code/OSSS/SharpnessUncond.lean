/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.SharpnessFK
import Theorem.StatisticalMechanics.Code.OSSS.RevealmentConstruction.Part7
import Theorem.StatisticalMechanics.Code.OSSS.TreeComplete.Part5
import Theorem.StatisticalMechanics.Code.FK.RussoDerivative.Part5
import Theorem.StatisticalMechanics.Code.OSSS.SharpnessUncond
open scoped BigOperators
open Finset
open Real Set
open StatMech.Lattice

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

open StatMech.OSSS

open StatMech.OSSS.CovLowerBound

open StatMech.OSSS.SharpnessFK

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.TreeComplete

open StatMech.OSSS.DecisionTree

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]


section Lattice

variable {d : ℕ}


def crossEvent (edge : E → Sym2 (Site d)) (o : Site d) (B : Set (Site d)) :
    Set (ConfigSpace E) :=
  {ω | ConnectedToSet d (liftCfg edge ω) o B}


end Lattice
end OSSS
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Revealment.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.OSSS.RevealmentConstruction
open scoped BigOperators
open Finset
open StatMech.Lattice

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace RevealmentConstruction

open StatMech.OSSS

open StatMech.OSSS.DecisionTree

open StatMech.OSSS.Revealment

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]


def runState {State : Type*} (guard : State → E → Bool) (step : State → E → Bool → State)
    (ω : ConfigSpace E) : List E → State → State
  | [], σ => σ
  | e :: rest, σ =>
      if guard σ e then runState guard step ω rest (step σ e (ω e))
      else runState guard step ω rest σ

end RevealmentConstruction
end OSSS
end StatMech

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


def buildTree {State : Type*} (guard : State → E → Bool) (step : State → E → Bool → State)
    (base : State → Bool) : List E → State → DecisionTree E
  | [], σ => DecisionTree.leaf (base σ)
  | e :: rest, σ =>
      if guard σ e then
        DecisionTree.node e (buildTree guard step base rest (step σ e true))
                            (buildTree guard step base rest (step σ e false))
      else
        buildTree guard step base rest σ

end RevealmentConstruction
end OSSS
end StatMech

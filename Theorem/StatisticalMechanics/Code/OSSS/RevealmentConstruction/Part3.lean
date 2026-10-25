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
import Inductive.StatisticalMechanics.Code.OSSS.RevealmentConstruction
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


variable {V : Type*} [DecidableEq V]


omit [Fintype E] [DecidableEq E] [DecidableEq V] in

theorem ReachOpen.trans {endU endV : E → V} {ω : ConfigSpace E} {x y z : V}
    (hxy : ReachOpen endU endV ω x y) (hyz : ReachOpen endU endV ω y z) :
    ReachOpen endU endV ω x z := by
  induction hxy with
  | refl => exact hyz
  | step e hopen hpair _ ih => exact ReachOpen.step e hopen hpair (ih hyz)


end RevealmentConstruction
end OSSS
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LocalizedCrossTree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.DecisionTreeReindex
import Theorem.StatisticalMechanics.Code.OSSS.FamilyEqzzzResolution
import Theorem.StatisticalMechanics.Code.OSSS.RevealmentCrossBox.Part7
import Theorem.StatisticalMechanics.Code.OSSS.ReachBoxCrossing.Part2
import Theorem.StatisticalMechanics.Code.OSSS.RevealmentTranslation
open scoped BigOperators


namespace StatMech

namespace OSSS

namespace LocalizedCrossTree

open DecisionTree LindebergTree Lindeberg

open RevealmentConstruction FamilyEqzzzResolution ReachBoxCrossing

open RevealmentTranslation

open Lattice

open scoped Classical

variable {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]

variable {d : Nat}


noncomputable def localizedBoxReveal (mu : ConfigSpace E -> Real) (iota : I -> E)
    (edge : I -> Sym2 (Site d)) (endU endV : I -> Site d)
    (k : Nat) (i : I) : Real :=
  mean mu (fun omega => if ConnectedToSet d
      (liftCfg edge (restrictConfig iota omega)) (endU i) (vertexBoundary d k)
    then (1 : Real) else 0)
  + mean mu (fun omega => if ConnectedToSet d
      (liftCfg edge (restrictConfig iota omega)) (endV i) (vertexBoundary d k)
    then (1 : Real) else 0)


end LocalizedCrossTree
end OSSS
end StatMech

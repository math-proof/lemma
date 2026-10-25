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
import Theorem.StatisticalMechanics.Code.OSSS.RevealmentConstruction.Part2
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


inductive ReachOpen (endU endV : E → V) (ω : ConfigSpace E) : V → V → Prop
  | refl (x : V) : ReachOpen endU endV ω x x
  | step {x y z : V} (e : E) (hopen : ω e = true)
      (hxy : (endU e = x ∧ endV e = y) ∨ (endU e = y ∧ endV e = x))
      (hrest : ReachOpen endU endV ω y z) : ReachOpen endU endV ω x z

end RevealmentConstruction
end OSSS
end StatMech

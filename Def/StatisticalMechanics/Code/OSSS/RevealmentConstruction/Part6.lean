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
import Theorem.StatisticalMechanics.Code.OSSS.RevealmentConstruction.Part6
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


section Lattice

variable {d : ℕ}


def ConnectedToSet (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (B : Set (Site d)) :
    Prop := ∃ b ∈ B, Connected d ω x b


noncomputable def liftCfg (edge : E → Sym2 (Site d)) (ω : ConfigSpace E) :
    ConfigSpace (Sym2 (Site d)) :=
  fun s => if h : ∃ e, edge e = s then ω h.choose else false

end Lattice
end RevealmentConstruction
end OSSS
end StatMech

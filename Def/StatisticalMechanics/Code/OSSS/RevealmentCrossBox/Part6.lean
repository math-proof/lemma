/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.TreeComplete.Part5
import Theorem.StatisticalMechanics.Code.OSSS.RevealmentCrossBox.Part6
open scoped BigOperators
open Finset
open StatMech.Lattice

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

open StatMech.OSSS.DecisionTree

open StatMech.OSSS.Revealment

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.TreeComplete

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {V : Type*} [DecidableEq V]


def xbCount (endU endV : E → V) (o : V) (l : List E) (disc₀ : Finset V) : ℕ :=
  2 * (xbUniverse endU endV o l disc₀).card


noncomputable def crossTree (endU endV : E → V) (o : V) (C : Set V)
    (l : List E) (disc₀ : Finset V) : DecisionTree E :=
  buildTree (xbGuard endU endV) (xbStep endU endV o)
    (fun s => decide (∃ y ∈ s.2, y ∈ C))
    (repeatList l (xbCount endU endV o l disc₀)) (disc₀, ∅)

end OSSS
end StatMech

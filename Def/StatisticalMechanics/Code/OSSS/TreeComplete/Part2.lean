/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.OSSS.RevealmentConstruction.Part7
import Theorem.StatisticalMechanics.Code.OSSS.TreeComplete.Part2
open scoped BigOperators
open Finset
open StatMech.Lattice

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace TreeComplete

open StatMech.OSSS

open StatMech.OSSS.DecisionTree

open StatMech.OSSS.Revealment

open StatMech.OSSS.RevealmentConstruction

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {V : Type*} [DecidableEq V]

def Saturated (endU endV : E → V) (ω : ConfigSpace E) (l : List E) (D : Finset V) : Prop :=
  ∀ e ∈ l, ω e = true → (endU e ∈ D ∨ endV e ∈ D) → endU e ∈ D ∧ endV e ∈ D

end TreeComplete
end OSSS
end StatMech

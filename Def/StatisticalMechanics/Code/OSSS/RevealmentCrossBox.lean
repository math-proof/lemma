/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.TreeComplete.Part5
import Abbrev.StatisticalMechanics.Code.OSSS.RevealmentCrossBox
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


def xbGuard (endU endV : E → V) (s : XState V) (e : E) : Bool :=
  decide (endU e ∈ s.1 ∨ endV e ∈ s.1)


def xbStep (endU endV : E → V) (o : V) (s : XState V) (e : E) (b : Bool) : XState V :=
  let D' := if b then insert (endU e) (insert (endV e) s.1) else s.1
  let D0a := if b ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2)
             then insert (endU e) (insert (endV e) s.2) else s.2
  let D0' := if o ∈ D' then insert o D0a else D0a
  (D', D0')

end OSSS
end StatMech

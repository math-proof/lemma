/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachDomination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.ReachBoxCrossing.Part2
open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace ReachDomination

open OSSS.Monotonic OSSS.AdaptMConditional StatMech.Probability

open StatMech.OSSS.MonotonicFK

open StatMech.OSSS.AdaptDisintegration

open OSSS.GrandCoupling OSSS.Coding

open StatMech.OSSS.RevealmentBoundAssembly

open StatMech.OSSS.RevealmentBoxCrossing

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.ReachBoxCrossing

open StatMech.Lattice

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {V : Type*} [DecidableEq V]


def IncidentCluster (endU endV : E → V) (X : ConfigSpace E) (B : Set V) (e' : E) : Prop :=
  ConnOpenSet endU endV X (endU e') B ∨ ConnOpenSet endU endV X (endV e') B


end ReachDomination
end OSSS
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachDomination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.ReachBoxCrossing.Part2
import Theorem.StatisticalMechanics.Code.OSSS.ReachDomination
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


def ClusterMeasurable (f : ConfigSpace E → ℝ) (endU endV : E → V) (B : Set V) : Prop :=
  ∀ X w : ConfigSpace E,
    (∀ e', IncidentCluster endU endV X B e' → w e' = X e') → f w = f X


noncomputable def indicatorConn (endU endV : E → V) (B C : Set V) (X : ConfigSpace E) : ℝ :=
  if ∃ x ∈ C, ConnOpenSet endU endV X x B then (1 : ℝ) else 0

end ReachDomination
end OSSS
end StatMech

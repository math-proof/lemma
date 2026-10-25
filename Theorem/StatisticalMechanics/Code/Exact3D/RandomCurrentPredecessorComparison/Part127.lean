/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part119
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical_of_emptyInnerSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical
    (hcover :
      ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hcover β hβpos hβc) fun n hn =>
    fun v hvwedge hlt hypos e0 hedge Ω S hS ew hew =>
      exactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt_of_emptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
        (β := β) (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (hn v hvwedge hlt hypos e0 hedge Ω S hS ew hew)

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsPositiveSubcritical_of_emptyInnerSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical
    (hcover :
      ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hcover β hβpos hβc) fun n hn =>
    fun v hvwedge hlt hypos e0 hedge Ω S hS ew hew =>
      exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt_of_emptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
        (β := β) (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (hn v hvwedge hlt hypos e0 hedge Ω S hS ew hew)

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsPositiveSubcritical_of_emptyInnerSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical
    (hcover :
      ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical) :
    ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hcover β hβpos hβc) fun n hn =>
    fun v hvwedge hlt hypos e0 hedge Ω S hS ew hew =>
      (exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellRouteShareBoundsAt_of_coverRouteShareBoundsAt
        (β := β) (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (hn v hvwedge hlt hypos e0 hedge Ω S hS ew hew)).1

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsPositiveSubcritical_of_emptyInnerSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical
    (hcover :
      ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hcover β hβpos hβc) fun n hn =>
    fun v hvwedge hlt hypos e0 hedge Ω S hS ew hew =>
      (exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellRouteShareBoundsAt_of_coverRouteShareBoundsAt
        (β := β) (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (hn v hvwedge hlt hypos e0 hedge Ω S hS ew hew)).2

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySourceEquationRouteShareBoundsPositiveSubcritical_of_emptySourceEquationCellRouteShareBoundsPositiveSubcritical
    (hcell :
      ExactSupportOwnerResidualSourcePairEmptySourceEquationCellRouteShareBoundsPositiveSubcritical) :
    ExactSupportOwnerResidualSourcePairEmptySourceEquationRouteShareBoundsPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hcell β hβpos hβc) fun n hn =>
    exactSupportOwnerResidualSourcePairEmptySourceEquationRouteShareBoundsAt_of_forall_emptySourceEquationCellRouteShareBoundsAt
      hn

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationRouteShareBoundsPositiveSubcritical_of_innerPairSourceEquationCellRouteShareBoundsPositiveSubcritical
    (hcell :
      ExactSupportOwnerResidualSourcePairInnerPairSourceEquationCellRouteShareBoundsPositiveSubcritical) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationRouteShareBoundsPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hcell β hβpos hβc) fun n hn =>
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationRouteShareBoundsAt_of_forall_innerPairSourceEquationCellRouteShareBoundsAt
      hn

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairSourceEquationRouteShareBoundsPositiveSubcritical_of_empty_innerSourceEquationCellRouteShareBoundsPositiveSubcritical
    (hempty :
      ExactSupportOwnerResidualSourcePairEmptySourceEquationCellRouteShareBoundsPositiveSubcritical)
    (hinner :
      ExactSupportOwnerResidualSourcePairInnerPairSourceEquationCellRouteShareBoundsPositiveSubcritical) :
    ExactSupportOwnerResidualSourcePairSourceEquationRouteShareBoundsPositiveSubcritical := by
  intro β hβpos hβc
  classical
  filter_upwards
    [(exactSupportOwnerResidualSourcePairEmptySourceEquationRouteShareBoundsPositiveSubcritical_of_emptySourceEquationCellRouteShareBoundsPositiveSubcritical
        hempty) β hβpos hβc,
      (exactSupportOwnerResidualSourcePairInnerPairSourceEquationRouteShareBoundsPositiveSubcritical_of_innerPairSourceEquationCellRouteShareBoundsPositiveSubcritical
        hinner) β hβpos hβc] with n hnEmpty hnInner
  exact
    exactSupportOwnerResidualSourcePairSourceEquationRouteShareBoundsAt_of_empty_innerSourceEquationRouteShareBoundsAt
      hnEmpty hnInner

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairSourceEquationRouteShareBoundsPositiveSubcritical_of_empty_innerSourceEquationRouteShareBoundsPositiveSubcritical
    (hempty :
      ExactSupportOwnerResidualSourcePairEmptySourceEquationRouteShareBoundsPositiveSubcritical)
    (hinner :
      ExactSupportOwnerResidualSourcePairInnerPairSourceEquationRouteShareBoundsPositiveSubcritical) :
    ExactSupportOwnerResidualSourcePairSourceEquationRouteShareBoundsPositiveSubcritical := by
  intro β hβpos hβc
  classical
  filter_upwards [hempty β hβpos hβc, hinner β hβpos hβc] with
    n hnEmpty hnInner
  exact
    exactSupportOwnerResidualSourcePairSourceEquationRouteShareBoundsAt_of_empty_innerSourceEquationRouteShareBoundsAt
      hnEmpty hnInner

end Exact3D
end StatMech

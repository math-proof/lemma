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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part118
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsPositiveSubcritical_of_emptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical
    (hsource :
      ExactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical) :
    ExactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hsource β hβpos hβc) fun n hn =>
    fun v hvwedge hlt hypos e0 hedge Ω S hS ew hew =>
      exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt_of_emptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsAt
        (β := β) (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (hn v hvwedge hlt hypos e0 hedge Ω S hS ew hew)

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsPositiveSubcritical_of_sourceEquationFiniteCellRouteShareBoundsPositiveSubcritical
    (hsource :
      ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsPositiveSubcritical) :
    ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hsource β hβpos hβc) fun n hn =>
    fun v hvwedge hlt hypos e0 hedge Ω S hS ew hew =>
      exactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt_of_sourceEquationFiniteCellRouteShareBoundsAt
        (β := β) (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (hn v hvwedge hlt hypos e0 hedge Ω S hS ew hew)

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsPositiveSubcritical_of_sourceEquationFiniteCellRouteShareBoundsPositiveSubcritical
    (hsource :
      ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsPositiveSubcritical) :
    ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hsource β hβpos hβc) fun n hn =>
    fun v hvwedge hlt hypos e0 hedge Ω S hS ew hew =>
      exactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt_of_sourceEquationFiniteCellRouteShareBoundsAt
        (β := β) (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (hn v hvwedge hlt hypos e0 hedge Ω S hS ew hew)

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsPositiveSubcritical_of_emptyInnerSplitDataFiniteCellCoverRouteShareBoundsPositiveSubcritical
    (hcover :
      ExactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsPositiveSubcritical) :
    ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hcover β hβpos hβc) fun n hn =>
    fun v hvwedge hlt hypos e0 hedge Ω S hS ew hew =>
      (exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellRouteShareBoundsAt_of_coverRouteShareBoundsAt
        (β := β) (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (hn v hvwedge hlt hypos e0 hedge Ω S hS ew hew)).1

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsPositiveSubcritical_of_emptyInnerSplitDataFiniteCellCoverRouteShareBoundsPositiveSubcritical
    (hcover :
      ExactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsPositiveSubcritical) :
    ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hcover β hβpos hβc) fun n hn =>
    fun v hvwedge hlt hypos e0 hedge Ω S hS ew hew =>
      (exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellRouteShareBoundsAt_of_coverRouteShareBoundsAt
        (β := β) (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (hn v hvwedge hlt hypos e0 hedge Ω S hS ew hew)).2

end Exact3D
end StatMech

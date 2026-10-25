/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedSupportInteraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDisjointWinding.Part4
open Finset


namespace StatMech.FrontierD

open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

instance : Fact (2 < L) :=
  ⟨lt_trans (by omega) (Fact.out : 8 < L)⟩


end
end StatMech.FrontierD

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisjointWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part7
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

def FKRectDartListUsesPoint {L : Nat} (l : List (ons_Dart L))
    (p : ZMod L × ZMod L) : Prop :=
  ∃ d ∈ l, d.1 = p ∨ ons_dirStep L d.2 d.1 = p

end
end StatMech.FrontierD

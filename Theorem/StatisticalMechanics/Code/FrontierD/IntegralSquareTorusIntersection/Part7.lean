/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Def.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part7
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


theorem dart_divergence
    (d : ons_Dart L) (p : ZMod L × ZMod L) :
    dartHorizontal d p + dartVertical d p -
        dartHorizontal d (p.1 - 1, p.2) -
        dartVertical d (p.1, p.2 - 1) =
      pointMass d.1 p - pointMass (ons_dirStep L d.2 d.1) p := by
  classical
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu <;>
    simp [dartHorizontal, dartVertical, ons_dirStep,
      pointMass_west, pointMass_south] <;> ring


end IntegralSquareTorusCycle
end
end StatMech.FrontierD

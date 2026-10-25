/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusResiduePotential
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveParity
open scoped BigOperators


namespace StatMech.Onsager

open StatMech.FrontierD

open StatMech.FrontierD.IntegralSquareTorusCycle

noncomputable section

def ons_positiveHorizontalSource {L : Nat} (d : ons_Dart L) :
    ZMod L × ZMod L :=
  if d.2 = 2 then (d.1.1 - 1, d.1.2) else d.1


def ons_positiveVerticalSource {L : Nat} (d : ons_Dart L) :
    ZMod L × ZMod L :=
  if d.2 = 3 then (d.1.1, d.1.2 - 1) else d.1

end
end StatMech.Onsager

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusResiduePotential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part9
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


def residuePotential (C : IntegralSquareTorusCycle L) (p : Nat) [NeZero p]
    (z : ZMod L × ZMod L) : ZMod p :=
  C.streamPotential z


def residueHorizontalCoeff (C : IntegralSquareTorusCycle L)
    (p : Nat) [NeZero p] (z : ZMod L × ZMod L) : Int :=
  ((C.residuePotential p z).val : Int) -
    (C.residuePotential p (z.1, z.2 - 1)).val


def residueVerticalCoeff (C : IntegralSquareTorusCycle L)
    (p : Nat) [NeZero p] (z : ZMod L × ZMod L) : Int :=
  ((C.residuePotential p (z.1 - 1, z.2)).val : Int) -
    (C.residuePotential p z).val

end IntegralSquareTorusCycle
end
end StatMech.FrontierD

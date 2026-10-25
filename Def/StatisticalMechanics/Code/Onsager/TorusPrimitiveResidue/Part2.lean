/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusResiduePotential
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveParity
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveResidue
open scoped BigOperators


namespace StatMech.Onsager

open StatMech.FrontierD

open StatMech.FrontierD.IntegralSquareTorusCycle

noncomputable section

def ons_residueOutgoingCoeff {L : Nat} [Fact (2 < L)]
    (C : IntegralSquareTorusCycle L) (p : Nat) [NeZero p]
    (z : ZMod L × ZMod L) (mu : Fin 4) : Int :=
  match mu.val with
  | 0 => C.residueHorizontalCoeff p z
  | 1 => C.residueVerticalCoeff p z
  | 2 => -C.residueHorizontalCoeff p (z.1 - 1, z.2)
  | _ => -C.residueVerticalCoeff p (z.1, z.2 - 1)

end
end StatMech.Onsager

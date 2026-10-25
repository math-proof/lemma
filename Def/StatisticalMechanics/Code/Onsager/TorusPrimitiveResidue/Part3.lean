/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusResiduePotential
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveParity
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveResidue.Part2
open scoped BigOperators


namespace StatMech.Onsager

open StatMech.FrontierD

open StatMech.FrontierD.IntegralSquareTorusCycle

noncomputable section

def ons_residueLoopCoeff {L n : Nat} [Fact (2 < L)] [NeZero n]
    (C : IntegralSquareTorusCycle L) (p : Nat) [NeZero p]
    (v : Fin n → ons_Dart L) (k : Fin n) : Int :=
  ons_residueOutgoingCoeff C p (ons_liftSite v k) (ons_liftDir v k)

end
end StatMech.Onsager

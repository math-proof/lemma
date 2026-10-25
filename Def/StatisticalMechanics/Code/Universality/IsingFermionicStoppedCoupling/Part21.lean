/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part16


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def sourceFailureCover
    (R level rho t : Nat) (p : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hlevel : 0 < level) (hlevelR : level < R) (hρ : 0 < rho)
    (hbottom : rho ≤ p.2.1) (htop : p.2.1 + rho ≤ R) :
    IsingStoppedCouplingSourceFailureFamily R t p (level : Int) →
      IsingLeapfrogHorizontalEscapeFamily level t ⊕
        IsingTransverseRaceWitnessFamily rho t (level : Int) := fun w => by
  classical
  by_cases hh : ∃ z : IsingLeapfrogHorizontalEscapeFamily level t, z.1 = w.1
  · exact Sum.inl (Classical.choose hh)
  · exact Sum.inr (Classical.choose
      ((sourceFailure_horizontal_or_transverse R level rho t p hstart hlevel
        hlevelR hρ hbottom htop w).resolve_left hh))

def sourceFailureCoverValue (level rho t : Nat) :
    IsingLeapfrogHorizontalEscapeFamily level t ⊕
        IsingTransverseRaceWitnessFamily rho t (level : Int) →
      IsingLeapfrogChoiceStringFamily t
  | Sum.inl z => z.1
  | Sum.inr z => transverseRaceWitnessValue rho t (level : Int) z

end
end StatMech.Universality

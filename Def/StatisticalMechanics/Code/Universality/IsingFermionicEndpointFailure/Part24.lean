/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicOrderedEndpointConvolution
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTailEndpointRace
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part21


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def IsingSourceChoiceNoHitOutputAtFamily
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    (forall k, k <= t -> lineFreeEndpoint (isingLeapfrogBoxInt p).1
      ((w.1.map Prod.fst).take k) ≠ level) /\
    isingLeapfrogChoiceRun R p w.1 = q}

def IsingMirrorChoiceNoHitOutputAtFamily
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    (forall k, k <= t -> lineFreeEndpoint (isingLeapfrogBoxInt p).1
      ((w.1.map Prod.fst).take k) ≠ level) /\
    isingLeapfrogChoiceRun R p'
      (isingLeapfrogCouplingChoiceTransform t
        (isingLeapfrogBoxInt p) level w).1 = q}

end
end StatMech.Universality

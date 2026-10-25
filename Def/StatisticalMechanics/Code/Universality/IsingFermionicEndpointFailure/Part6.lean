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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part5


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def endpointFarEscapeWitnessValue
    (m t : Nat) (start target : Int) :
    IsingEndpointFarEscapeWitnessFamily m t start target →
      IsingLeapfrogChoiceStringFamily t := fun z =>
  ⟨(z.2.1.1.zip z.2.2.1.1) ++ z.2.2.2.1, by
    rw [List.length_append, List.length_zip, z.2.1.2.1,
      z.2.2.1.2.1, z.2.2.2.2]
    simp
    omega⟩

end
end StatMech.Universality

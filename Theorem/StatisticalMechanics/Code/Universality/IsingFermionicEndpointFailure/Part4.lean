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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part4


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem exists_sourceFailureOutputTransverseCover
    (R level rho t : Nat) (p q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hρ : 0 < rho) (hbottom : rho <= p.2.1)
    (htop : p.2.1 + rho <= R)
    (hqVertical : q.2.1 = 0 \/ q.2.1 = R)
    (w : IsingSourceFailureOutputAtFamily R t p q (level : Int)) :
    exists u : IsingTailDependentEndpointRaceFamily rho t (level : Int)
        (sourceEndpointRaceTarget R t rho p q),
      tailDependentEndpointRaceValue R t rho p q (level : Int) u = w.1.1 := by
  rcases exists_sourceFailureOutput_transverseWitness R level rho t p q hstart
    hρ hbottom htop hqVertical w with ⟨z, hz, hmark⟩
  let endpointWord : IsingHorizontalNoHitEndpointFamily z.1 (level : Int)
      (sourceEndpointRaceTarget R t rho p q z.1 z.2.2.1 z.2.2.2) :=
    ⟨z.2.1, sourceEndpointRaceTarget_eq R level rho t p q hstart
      hqVertical w z hz hmark⟩
  let u : IsingTailDependentEndpointRaceFamily rho t (level : Int)
      (sourceEndpointRaceTarget R t rho p q) :=
    ⟨z.1, z.2.2.1, z.2.2.2, endpointWord⟩
  refine ⟨u, ?_⟩
  apply Subtype.ext
  have hvalue := congrArg
    (fun v : IsingLeapfrogChoiceStringFamily t => v.1) hz
  simpa [tailDependentEndpointRaceValue, transverseRaceWitnessValue,
    u, endpointWord] using hvalue

end
end StatMech.Universality

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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part10


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem exists_sourceFailureAtAlignedCover_of_rightHalf
    (R level t : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hlevelR : level < R) (hhalf : R <= 2 * level)
    (w : IsingStoppedCouplingSourceFailureAtFamily R t p p' q
      (level : Int)) :
    exists z : Sum (IsingSourceFailureOutputAtFamily R t p q (level : Int))
        (IsingMirrorFailureOutputAtFamily R t p p' q (level : Int)),
      alignedFailureOutputValue R t p p' q (level : Int) z = w.1 := by
  rcases w.2.2 with hsourceOutput | hmirrorOutput
  · exact ⟨Sum.inl ⟨⟨w.1, w.2.1⟩, hsourceOutput⟩, rfl⟩
  · let ws : IsingStoppedCouplingSourceFailureFamily R t p (level : Int) :=
      ⟨w.1, w.2.1⟩
    have hm := sourceFailure_implies_mirrorFailure_of_rightHalf R level t p p'
      hstart hmirror hlevelR hhalf ws
    exact ⟨Sum.inr ⟨⟨w.1, hm⟩, hmirrorOutput⟩, rfl⟩

end
end StatMech.Universality

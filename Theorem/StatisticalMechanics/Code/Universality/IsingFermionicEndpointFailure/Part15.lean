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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part18


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem exists_mirrorFailureAtAlignedOrResidualCover
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int)
    (w : IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level) :
    exists z : Sum (IsingSourceFailureOutputAtFamily R t p q level)
        (Sum (IsingMirrorFailureOutputAtFamily R t p p' q level)
          (IsingMirrorOnlySourceOutputAtFamily R t p p' q level)),
      endpointFailureAlignedOrResidualValue R t p p' q level z = w.1 := by
  rcases w.2.2 with hsourceOutput | hmirrorOutput
  · by_cases hs : IsingStoppedCouplingSourceFailure R p level w.1
    · exact ⟨Sum.inl ⟨⟨w.1, hs⟩, hsourceOutput⟩, rfl⟩
    · exact ⟨Sum.inr (Sum.inr ⟨w.1, w.2.1, hs, hsourceOutput⟩), rfl⟩
  · exact ⟨Sum.inr (Sum.inl ⟨⟨w.1, w.2.1⟩, hmirrorOutput⟩), rfl⟩

end
end StatMech.Universality

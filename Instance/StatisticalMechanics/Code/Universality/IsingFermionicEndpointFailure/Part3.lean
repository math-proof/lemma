module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part4
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicOrderedEndpointConvolution
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTailEndpointRace
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part12


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable instance isingMirrorOnlySourceOutputAtFamily_finite
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Finite (IsingMirrorOnlySourceOutputAtFamily R t p p' q level) := by
  exact Finite.of_injective Subtype.val Subtype.val_injective


end
end StatMech.Universality

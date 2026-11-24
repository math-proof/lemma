module
public import Theorem.StatisticalMechanics.Code.Universality.HexEndpointCyclicAtomSupport


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointTripletOrbit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk

noncomputable section

def hexEndpointCanonicalTripletPiece (base : List ℤ) : Finset (List ℤ) :=
  {base, base ++ [-1], base ++ [1]}


end
end StatMech.Universality

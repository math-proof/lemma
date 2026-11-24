module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

def VerticalChoicePathFamily (t : Nat) (x y : Int) :=
  {bs : List Bool // bs.length = t ∧ lineFreeEndpoint x bs = y}

end IsingDiagonalWalkHitSplit
end StatMech.Universality

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part8


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

noncomputable instance boolListLength_finite (t : Nat) :
    Finite {v : List Bool // v.length = t} :=
  List.finite_length_eq Bool t

end IsingDiagonalWalkHitSplit
end StatMech.Universality

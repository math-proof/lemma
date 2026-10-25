/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAxisStaircaseApproximation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicAxisStaircaseApproximation
open Filter Set Topology


namespace StatMech.Universality

noncomputable section

def axisTwoEdgeStaircaseBaseSet
    (x y mesh : Real) (width height : Nat) : Set Complex :=
  {a | Or
    (exists k, k < width /\
      a = (x + (k : Real) * mesh : Real) + y * Complex.I)
    (Or
      (exists k, k < height /\
        a = (x + (width : Real) * mesh : Real) +
          (y + (k : Real) * mesh : Real) * Complex.I)
      (Or
        (exists k, k < width /\
          a = (x + (width : Real) * mesh - (k : Real) * mesh : Real) +
            (y + (height : Real) * mesh : Real) * Complex.I)
        (exists k, k < height /\
          a = x + (y + (height : Real) * mesh - (k : Real) * mesh : Real) *
            Complex.I)))}


end
end StatMech.Universality

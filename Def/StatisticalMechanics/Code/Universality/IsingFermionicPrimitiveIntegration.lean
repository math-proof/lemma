/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitiveIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitive.Part2
open Finset


namespace StatMech.Universality

noncomputable section

def IsingRectangleClosedOneForm
    (horizontal vertical : Nat -> Nat -> Real) : Prop :=
  forall i j,
    vertical i j + horizontal i (j + 1) =
      horizontal i j + vertical (i + 1) j


def isingRectanglePrimitive
    (horizontal vertical : Nat -> Nat -> Real) (i j : Nat) : Real :=
  (∑ k ∈ range i, horizontal k 0) +
    ∑ l ∈ range j, vertical i l


def isingRectanglePrimitiveWithBase
    (base : Real) (horizontal vertical : Nat -> Nat -> Real)
    (i j : Nat) : Real :=
  base + isingRectanglePrimitive horizontal vertical i j

end
end StatMech.Universality

module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part22
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFourthMoment.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

noncomputable section

def isingLineCenteredFourth
    (m : Nat) (q : IsingLineBox (2 * m)) : Real :=
  ((q.1 : Real) - (m : Real)) ^ 4

end
end StatMech.Universality

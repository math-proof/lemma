module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicWeightedDirichletComparison.Part6
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFiniteGhostComparison.Part2
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

noncomputable section

noncomputable def isingFermionicGhostRate
    {V : Type*} (boundaryMultiplicity : V → Nat) : V → Real :=
  fun x ↦ isingFermionicGhostCoefficient * boundaryMultiplicity x

end
end StatMech.Universality

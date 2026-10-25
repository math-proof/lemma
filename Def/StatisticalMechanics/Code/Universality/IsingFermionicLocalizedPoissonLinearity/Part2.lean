/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointLocalizedRobinConsistency.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalizedPoissonLinearity.Part2


namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

noncomputable def isingFiniteWeightedInteriorExceptionalSources
    {V : Type*} [Fintype V]
    (boundary exceptional : V -> Prop) : Finset V := by
  classical
  exact univ.filter fun z => ¬ boundary z ∧ exceptional z

end
end StatMech.Universality

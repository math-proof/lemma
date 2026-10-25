/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRobinCompatibility.Part3


namespace StatMech.Universality

open Finset SimpleGraph Filter Metric Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def isingFiniteWeightedLocalizedPoissonBarrier
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary exceptional : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b) : V -> Real := by
  classical
  exact isingFiniteWeightedDirichletSolve G conductance boundary
    hconductance hpositive hhit
    (fun x => if boundary x then 0 else if exceptional x then -1 else 0)

end
end StatMech.Universality

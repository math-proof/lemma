/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareDirichletConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
open Finset SimpleGraph Filter Set Topology


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareBoxBoundary (n : Nat) (x : (fkSquareBoxPlanar n).V) : Prop :=
  ∃ i : Fin 2, (x.1 i).natAbs = n

end
end StatMech.Universality

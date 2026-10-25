/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc33escaping.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc34ray
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def ray34_KState {V : Type*} (G : SimpleGraph V) : Type _ :=
  { p : Set V × V // p.2 ∉ p.1 ∧ (ray34_AvoidCluster G p.1 p.2).Infinite }


noncomputable def ray34_kstep {V : Type*} [DecidableEq V] (G : SimpleGraph V) [LocallyFinite G]
    (s : ray34_KState G) : ray34_KState G :=
  ⟨(insert s.1.2 s.1.1, (ray34_konig_step s.2.1 s.2.2).choose),
    ray34_notMem_of_avoidCluster_nonempty
      (ray34_konig_step s.2.1 s.2.2).choose_spec.2.2.2.nonempty,
    (ray34_konig_step s.2.1 s.2.2).choose_spec.2.2.2⟩


end StatMech.Walls

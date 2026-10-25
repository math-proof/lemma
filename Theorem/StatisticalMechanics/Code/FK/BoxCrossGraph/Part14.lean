/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.FK.BoxCrossGraph.Part14
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


theorem isAnnulusWiring_boxBoundary_succ (d n : ℕ) :
    IsAnnulusWiring d n
      (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n+1))) := by
  intro u v hadj
  rw [StatMech.Lattice.boundaryCliqueGraph_adj] at hadj
  exact (boxBoundary_succ_iff_not_inner d n u).mp hadj.2.1


end FK
end StatMech

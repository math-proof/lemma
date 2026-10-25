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
import Def.StatisticalMechanics.Code.FK.BoxCrossGraph.Part10
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


theorem crossShift_pos {d n : ℕ} {p q : ℝ} (hp1 : p < 1) (hq : 0 < q) :
    0 < crossShift d n p q :=
  mul_pos (pow_pos (by linarith) _) (pow_pos hq _)


theorem bcWeight_crossExt (d n : ℕ) {p q : ℝ} (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    bcWeight (boxGraph d (n+1)) (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n)) p q
        (crossExt d n ω)
      = wiredFkWeight (boxGraph d n) (boxBoundary d n) p q ω * crossShift d n p q := by
  rw [bcWeight, numClustersBC_boundaryClique, numClustersWired_crossExt,
    edgeProduct_crossExt, wiredFkWeight, crossShift, pow_add]
  ring


end FK
end StatMech

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
import Abbrev.StatisticalMechanics.Code.FK.BoxCrossGraph
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


def innerWiredHom (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    (innerWiredGraph d n ω) →g (crossWiredGraph d n ω) where
  toFun := boxVertIncl d n
  map_rel' := fun {a b} hab => (crossWiredGraph_adj_boxVertIncl d n ω a b).mpr hab


noncomputable def crossComponentEquivFun (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    (innerWiredGraph d n ω).ConnectedComponent ⊕
      {v : boxVerts d (n+1) // ¬ IsInnerVert d n v} →
      (crossWiredGraph d n ω).ConnectedComponent
  | Sum.inl c => c.map (innerWiredHom d n ω)
  | Sum.inr v => (crossWiredGraph d n ω).connectedComponentMk v.1


end FK
end StatMech

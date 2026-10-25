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
import Theorem.StatisticalMechanics.Code.FK.BoxCrossGraph.Part16
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


def innerWiredHomAdd (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    {D : SimpleGraph (boxVerts d (n+1))} (hD : IsAnnulusWiring d n D) :
    (innerWiredGraph d n ω) →g (crossWiredGraphAdd d n ω D) where
  toFun := boxVertIncl d n
  map_rel' := fun {a b} hab => (crossWiredGraphAdd_adj_boxVertIncl d n ω hD a b).mpr hab


def annulusHomAdd (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (D : SimpleGraph (boxVerts d (n+1))) :
    (annulusSubgraph d n D) →g (crossWiredGraphAdd d n ω D) where
  toFun := Subtype.val
  map_rel' := fun {a b} hab => (crossWiredGraphAdd_adj_annulus d n ω D a b).mpr hab


noncomputable def crossComponentEquivAddFun (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) :
    (innerWiredGraph d n ω).ConnectedComponent ⊕
      (annulusSubgraph d n D).ConnectedComponent →
      (crossWiredGraphAdd d n ω D).ConnectedComponent
  | Sum.inl c => c.map (innerWiredHomAdd d n ω hD)
  | Sum.inr a => a.map (annulusHomAdd d n ω D)

end FK
end StatMech

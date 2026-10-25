/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/VSeparates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.HVIntersection.Part2
open Set SimpleGraph


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box


def projHom (ω : ConfigSpace (Sym2 (Site 2))) (R : Set (Site 2)) :
    (openSubgraphInduce 2 ω R) →g (hypercubicLattice 2) where
  toFun := fun v => (v : Site 2)
  map_rel' := by
    intro a b hab
    simp only [openSubgraphInduce_adj] at hab
    exact openSubgraph_le ω hab


def liftWalk (ω : ConfigSpace (Sym2 (Site 2))) (R : Set (Site 2)) {x y : R}
    (w : (openSubgraphInduce 2 ω R).Walk x y) :
    (hypercubicLattice 2).Walk (x : Site 2) (y : Site 2) :=
  w.map (projHom ω R)


end Universality
end StatMech

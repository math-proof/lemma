/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part2
open MeasureTheory

set_option linter.style.show false


namespace StatMech

namespace Percolation

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


def translateHom (g : Multiplicative (Site d)) (ω : ConfigSpace (Sym2 (Site d))) :
    openSubgraph d ω →g openSubgraph d (shift g ω) where
  toFun x := g • x
  map_rel' {x y} h := (openSubgraph_adj_shift g ω x y).mpr h


def translateHomInv (g : Multiplicative (Site d)) (ω : ConfigSpace (Sym2 (Site d))) :
    openSubgraph d (shift g ω) →g openSubgraph d ω where
  toFun a := g⁻¹ • a
  map_rel' {a b} h := by
    have h' := (openSubgraph_adj_shift g ω (g⁻¹ • a) (g⁻¹ • b)).mp
    simp only [smul_inv_smul] at h'
    exact h' h

end Percolation
end StatMech

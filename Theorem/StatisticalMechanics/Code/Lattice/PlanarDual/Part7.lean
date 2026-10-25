/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.PlanarDual.Part7
open SimpleGraph


namespace StatMech

namespace Lattice

theorem crossingEdgeEquiv_coe (e : (hypercubicLattice 2).edgeSet) :
    (crossingEdgeEquiv e : Sym2 (Site 2)) = Sym2.map (⇑rot90Iso) e := by
  rw [crossingEdgeEquiv, SimpleGraph.Iso.mapEdgeSet]
  exact Hom.mapEdgeSet_coe rot90Iso.toHom e


theorem crossingEdgeEquiv_horizontal (a b : ℤ)
    (he : s(![a, b], ![a + 1, b]) ∈ (hypercubicLattice 2).edgeSet) :
    (crossingEdgeEquiv ⟨_, he⟩ : Sym2 (Site 2)) = s(![-b, a], ![-b, a + 1]) := by
  rw [crossingEdgeEquiv_coe]
  simp [Sym2.map_mk]


theorem crossingEdgeEquiv_vertical (a b : ℤ)
    (he : s(![a, b], ![a, b + 1]) ∈ (hypercubicLattice 2).edgeSet) :
    (crossingEdgeEquiv ⟨_, he⟩ : Sym2 (Site 2)) = s(![-b, a], ![-(b + 1), a]) := by
  rw [crossingEdgeEquiv_coe]
  simp [Sym2.map_mk]


end Lattice
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Graph.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part3
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


noncomputable def kwg_dualEnds (P : PlanarZ2Subgraph) (e : kwg_Edge P) :
    Sym2 (kwg_Face P) :=
  s((whb_faceRegion (imageGraph P)).connectedComponentMk (kwg_flankLeft P e),
    (whb_faceRegion (imageGraph P)).connectedComponentMk (kwg_flankRight P e))


noncomputable def kwg_dualGraph (P : PlanarZ2Subgraph) :
    Graph (kwg_Face P) (kwg_Edge P) where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e x y := kwg_dualEnds P e = s(x, y)
  isLink_symm := by
    intro e _ x y h
    simpa only [Sym2.eq_swap] using h
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y v w hxy hvw
    rw [hxy] at hvw
    exact (Sym2.eq_iff.mp hvw).elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  edge_mem_iff_exists_isLink := by
    intro e
    simp only [Set.mem_univ, true_iff]
    induction kwg_dualEnds P e with
    | _ x y => exact ⟨x, y, rfl⟩
  left_mem_of_isLink := by simp

end Ising
end StatMech

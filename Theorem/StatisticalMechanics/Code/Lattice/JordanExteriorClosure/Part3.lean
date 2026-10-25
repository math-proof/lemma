/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding.Part2
import Def.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part3
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box


@[simp] theorem jec_wallEdge_mk (z x y : Site 2) :
    jec_wallEdge z s(x, y) ↔
      (x 1 = y 1 ∧ x 1 ≤ z 1 - 1) ∧
      ((x 0 = z 0 - 1 ∧ y 0 = z 0) ∨ (y 0 = z 0 - 1 ∧ x 0 = z 0)) := by
  unfold jec_wallEdge; rfl


theorem jec_quad_bdEdge_iff (z u v : Site 2) (hadj : (hypercubicLattice 2).Adj u v) :
    bdEdge (jec_quad z) s(u, v) ↔ (jec_rayEdge z s(u, v) ∨ jec_wallEdge z s(u, v)) := by
  rw [bdEdge_mk, jec_rayEdge_mk, jec_wallEdge_mk]
  simp only [jec_mem_quad]
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  omega


theorem jec_ray_wall_excl (z u v : Site 2) :
    ¬ (jec_rayEdge z s(u, v) ∧ jec_wallEdge z s(u, v)) := by
  rw [jec_rayEdge_mk, jec_wallEdge_mk]; omega


end Lattice
end StatMech

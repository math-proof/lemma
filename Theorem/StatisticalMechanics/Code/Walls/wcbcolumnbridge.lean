/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcbcolumnbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
import Theorem.StatisticalMechanics.Code.Walls.wnuupperhalf.Part5
import Theorem.StatisticalMechanics.Code.Walls.wnaalternate.Part3
import Def.StatisticalMechanics.Code.Walls.wcbcolumnbridge
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

theorem wcb_rayEdge_column (z x y : Site 2) (h : jec_rayEdge z s(x, y)) :
    x 0 = y 0 := by
  rw [jec_rayEdge_mk] at h
  exact h.1.1


theorem wcb_rayEdge_eq_of_column (z x y : Site 2) (h : jec_rayEdge z s(x, y)) :
    s(x, y) = wcb_canonRayEdge z (x 0) := by
  rw [jec_rayEdge_mk] at h
  obtain ⟨⟨hxy, _hle⟩, hcase⟩ := h
  unfold wcb_canonRayEdge
  rcases hcase with ⟨hx1, hy1⟩ | ⟨hy1, hx1⟩
  · 
    have hx : x = ![x 0, z 1 - 1] := by
      ext i; fin_cases i <;> simp [hx1]
    have hy : y = ![x 0, z 1] := by
      ext i; fin_cases i <;> simp [hxy.symm, hy1]
    rw [hx, hy]; norm_num
  · 
    have hx : x = ![x 0, z 1] := by
      ext i; fin_cases i <;> simp [hx1]
    have hy : y = ![x 0, z 1 - 1] := by
      ext i; fin_cases i <;> simp [hxy.symm, hy1]
    rw [hx, hy, Sym2.eq_swap]; norm_num


theorem wcb_rayEdge_injOn_column (z x₁ y₁ x₂ y₂ : Site 2)
    (h₁ : jec_rayEdge z s(x₁, y₁)) (h₂ : jec_rayEdge z s(x₂, y₂))
    (hcol : x₁ 0 = x₂ 0) :
    s(x₁, y₁) = s(x₂, y₂) := by
  rw [wcb_rayEdge_eq_of_column z x₁ y₁ h₁, wcb_rayEdge_eq_of_column z x₂ y₂ h₂, hcol]


end Lattice
end StatMech

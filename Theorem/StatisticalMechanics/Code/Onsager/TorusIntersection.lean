/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Def.StatisticalMechanics.Code.Onsager.TorusIntersection


namespace StatMech.Onsager

open BigOperators StatMech.Ising

@[simp] theorem ons_edgeBit_eq_one_iff
    {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) (e : Sym2 V) :
    ons_edgeBit F e = 1 ↔ e ∈ F := by
  simp [ons_edgeBit]

@[simp] theorem ons_edgeBit_eq_zero_iff
    {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) (e : Sym2 V) :
    ons_edgeBit F e = 0 ↔ e ∉ F := by
  simp [ons_edgeBit]

theorem ons_portEdge_west_eq_horizontal
    (L : ℕ) (p : ZMod L × ZMod L) :
    ons_portEdge L (p, 2) =
      ons_portEdge L ((p.1 - 1, p.2), 0) := by
  rcases p with ⟨x, y⟩
  simp [ons_portEdge, ons_dirStep, Sym2.eq_iff]

theorem ons_portEdge_south_eq_vertical
    (L : ℕ) (p : ZMod L × ZMod L) :
    ons_portEdge L (p, 3) =
      ons_portEdge L ((p.1, p.2 - 1), 1) := by
  rcases p with ⟨x, y⟩
  simp [ons_portEdge, ons_dirStep, Sym2.eq_iff]


theorem ons_edgeBits_divergence_zero
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L))
    (p : ZMod L × ZMod L) :
    ons_horizontalBit F p + ons_horizontalBit F (p.1 - 1, p.2) +
      ons_verticalBit F p + ons_verticalBit F (p.1, p.2 - 1) = 0 := by
  have hsum := ons_evenSubgraph_neighbor_sum_zero
    (onsTorusGraph L) F hF p
  rw [ons_torus_neighbor_sum_eq_direction_sum] at hsum
  rw [Fin.sum_univ_four] at hsum
  change
    ons_edgeBit F (ons_portEdge L (p, 0)) +
      ons_edgeBit F (ons_portEdge L (p, 1)) +
      ons_edgeBit F (ons_portEdge L (p, 2)) +
      ons_edgeBit F (ons_portEdge L (p, 3)) = 0 at hsum
  rw [ons_portEdge_west_eq_horizontal,
    ons_portEdge_south_eq_vertical] at hsum
  change
    ons_horizontalBit F p + ons_verticalBit F p +
      ons_horizontalBit F (p.1 - 1, p.2) +
      ons_verticalBit F (p.1, p.2 - 1) = 0 at hsum
  simpa [add_assoc, add_left_comm, add_comm] using hsum


end StatMech.Onsager

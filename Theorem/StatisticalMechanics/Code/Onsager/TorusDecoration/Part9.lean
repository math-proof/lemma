/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.TrivalentCycles
import Theorem.StatisticalMechanics.Code.Onsager.TurningTelescope.Part3
import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Def.StatisticalMechanics.Code.Onsager.TorusDecoration.Part9


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

theorem ons_decorated_local_even (L : ℕ) [Fact (2 < L)]
    (D : Finset (Sym2 (ons_Dart L)))
    (hD : D ∈ evenSubgraphs (ons_decGraph L))
    (s : ZMod L × ZMod L) :
    ons_decChainEven
      (ons_decoratedPortBit D (s, 0)) (ons_decoratedPortBit D (s, 1))
      (ons_decoratedPortBit D (s, 2)) (ons_decoratedPortBit D (s, 3))
      (ons_decoratedChainBits D s) := by
  have h0 := ons_evenSubgraph_neighbor_sum_zero
    (ons_decGraph L) D hD (s, (0 : Fin 4))
  have h1 := ons_evenSubgraph_neighbor_sum_zero
    (ons_decGraph L) D hD (s, (1 : Fin 4))
  have h2 := ons_evenSubgraph_neighbor_sum_zero
    (ons_decGraph L) D hD (s, (2 : Fin 4))
  have h3 := ons_evenSubgraph_neighbor_sum_zero
    (ons_decGraph L) D hD (s, (3 : Fin 4))
  rw [ons_decGraph_neighborFinset,
    Finset.sum_insert (ons_dartRev_not_mem_internalNeighbors L (s, (0 : Fin 4)))] at h0
  rw [ons_decGraph_neighborFinset,
    Finset.sum_insert (ons_dartRev_not_mem_internalNeighbors L (s, (1 : Fin 4)))] at h1
  rw [ons_decGraph_neighborFinset,
    Finset.sum_insert (ons_dartRev_not_mem_internalNeighbors L (s, (2 : Fin 4)))] at h2
  rw [ons_decGraph_neighborFinset,
    Finset.sum_insert (ons_dartRev_not_mem_internalNeighbors L (s, (3 : Fin 4)))] at h3
  rw [show ons_decInternalNeighbors (s, (0 : Fin 4)) = {(s, (1 : Fin 4))} from rfl,
    Finset.sum_singleton] at h0
  rw [show ons_decInternalNeighbors (s, (1 : Fin 4)) =
      {(s, (0 : Fin 4)), (s, (2 : Fin 4))} from rfl,
    Finset.sum_insert (by simp), Finset.sum_singleton] at h1
  rw [show ons_decInternalNeighbors (s, (2 : Fin 4)) =
      {(s, (1 : Fin 4)), (s, (3 : Fin 4))} from rfl,
    Finset.sum_insert (by simp), Finset.sum_singleton] at h2
  rw [show ons_decInternalNeighbors (s, (3 : Fin 4)) = {(s, (2 : Fin 4))} from rfl,
    Finset.sum_singleton] at h3
  rw [show s((s, (1 : Fin 4)), (s, (0 : Fin 4))) =
      s((s, (0 : Fin 4)), (s, (1 : Fin 4))) from Sym2.eq_swap] at h1
  rw [show s((s, (2 : Fin 4)), (s, (1 : Fin 4))) =
      s((s, (1 : Fin 4)), (s, (2 : Fin 4))) from Sym2.eq_swap] at h2
  rw [show s((s, (3 : Fin 4)), (s, (2 : Fin 4))) =
      s((s, (2 : Fin 4)), (s, (3 : Fin 4))) from Sym2.eq_swap] at h3
  unfold ons_decChainEven
  constructor
  · simpa [ons_decoratedPortBit, ons_decoratedChainBits,
      ons_decInternalNeighbors] using h0
  constructor
  · simpa [ons_decoratedPortBit, ons_decoratedChainBits,
      ons_decInternalNeighbors, add_assoc] using h1
  constructor
  · simpa [ons_decoratedPortBit, ons_decoratedChainBits,
      ons_decInternalNeighbors, add_assoc] using h2
  · simpa [ons_decoratedPortBit, ons_decoratedChainBits,
      ons_decInternalNeighbors] using h3

end StatMech.Onsager

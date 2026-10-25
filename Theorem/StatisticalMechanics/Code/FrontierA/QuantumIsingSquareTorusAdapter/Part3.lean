/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingSquareTorusAdapter.Part3
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


theorem sum_squareTorus_edges_eq_positive_directions
    (L : Nat) [Fact (2 < L)]
    (f : Sym2 (ZMod L × ZMod L) → Real) :
    (∑ edge ∈ (onsTorusGraph L).edgeFinset, f edge) =
      ∑ p : ZMod L × ZMod L,
        (f (ons_portEdge L (p, 0)) + f (ons_portEdge L (p, 1))) := by
  have hsum := Equiv.sum_comp (squareTorusPositiveEdgeEquiv L)
    (fun edge : {edge // edge ∈ (onsTorusGraph L).edgeFinset} ↦ f edge.1)
  rw [Finset.sum_subtype (onsTorusGraph L).edgeFinset]
  · rw [← hsum]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro p _
    rw [Fin.sum_univ_two]
    rfl
  · intro edge
    rw [SimpleGraph.mem_edgeFinset]


theorem prod_squareTorus_edges_eq_positive_directions
    (L : Nat) [Fact (2 < L)]
    (f : Sym2 (ZMod L × ZMod L) → Real) :
    (∏ edge ∈ (onsTorusGraph L).edgeFinset, f edge) =
      ∏ p : ZMod L × ZMod L,
        (f (ons_portEdge L (p, 0)) * f (ons_portEdge L (p, 1))) := by
  have hprod := Equiv.prod_comp (squareTorusPositiveEdgeEquiv L)
    (fun edge : {edge // edge ∈ (onsTorusGraph L).edgeFinset} ↦ f edge.1)
  rw [Finset.prod_subtype (onsTorusGraph L).edgeFinset]
  · rw [← hprod]
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro p _
    rw [Fin.prod_univ_two]
    rfl
  · intro edge
    rw [SimpleGraph.mem_edgeFinset]


end StatMech.FrontierA

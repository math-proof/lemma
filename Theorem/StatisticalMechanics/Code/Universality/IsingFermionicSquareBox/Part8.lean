/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Mathlib.Combinatorics.SimpleGraph.Matching
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part7


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredExteriorStar_le_clique (n : Nat) :
    fkIsingSquareWiredExteriorStar n ≤
      boundaryCliqueGraph (fkIsingSquareWiredArc n) := by
  classical
  intro x y hxy
  rw [boundaryCliqueGraph_adj]
  exact ⟨hxy.1, hxy.2.1, hxy.2.2.1⟩


theorem fkIsingSquareWiredExteriorStar_reachable
    (n : Nat) {x y : (fkSquareBoxPlanar n).V}
    (hx : fkIsingSquareWiredArc n x)
    (hy : fkIsingSquareWiredArc n y) :
    (fkIsingSquareWiredExteriorStar n).Reachable x y := by
  by_cases hxy : x = y
  · subst y
    exact Reachable.refl _
  by_cases hxa : x = fkIsingSquareMarkedA n
  · exact (show (fkIsingSquareWiredExteriorStar n).Adj x y by
      exact ⟨hxy, hx, hy, Or.inl hxa⟩).reachable
  by_cases hya : y = fkIsingSquareMarkedA n
  · exact (show (fkIsingSquareWiredExteriorStar n).Adj x y by
      exact ⟨hxy, hx, hy, Or.inr hya⟩).reachable
  have hxa' : (fkIsingSquareWiredExteriorStar n).Adj x
      (fkIsingSquareMarkedA n) := by
    exact ⟨hxa, hx, fkIsingSquareMarkedA_mem_wiredArc n, Or.inr rfl⟩
  have hay : (fkIsingSquareWiredExteriorStar n).Adj
      (fkIsingSquareMarkedA n) y := by
    exact ⟨Ne.symm hya, fkIsingSquareMarkedA_mem_wiredArc n, hy,
      Or.inl rfl⟩
  exact hxa'.reachable.trans hay.reachable

theorem reachable_of_adj_reachable_square
    {V : Type*} {G K : SimpleGraph V}
    (hstep : ∀ {u v}, G.Adj u v → K.Reachable u v)
    {x y : V} (hxy : G.Reachable x y) : K.Reachable x y := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact Reachable.refl _
  | cons huv p ih => exact (hstep huv).trans ih


theorem fkIsingSquare_sup_wiredExteriorStar_reachable_iff_clique
    (n : Nat) (H : SimpleGraph (fkSquareBoxPlanar n).V)
    (x y : (fkSquareBoxPlanar n).V) :
    (H ⊔ fkIsingSquareWiredExteriorStar n).Reachable x y ↔
      (H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable x y := by
  classical
  constructor
  · exact fun h => h.mono (sup_le_sup_left
      (fkIsingSquareWiredExteriorStar_le_clique n) H)
  · intro h
    apply reachable_of_adj_reachable_square (G :=
      H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)) (K :=
      H ⊔ fkIsingSquareWiredExteriorStar n) ?_ h
    intro u v huv
    rcases huv with hH | hclique
    · exact Adj.reachable (show (H ⊔ fkIsingSquareWiredExteriorStar n).Adj u v from
        Or.inl hH)
    · rw [boundaryCliqueGraph_adj] at hclique
      exact (fkIsingSquareWiredExteriorStar_reachable n
        hclique.2.1 hclique.2.2).mono le_sup_right


end
end StatMech.Universality

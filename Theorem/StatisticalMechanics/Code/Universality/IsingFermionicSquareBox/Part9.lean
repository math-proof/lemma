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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part8


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredGadgetProjection_reachable
    (n : Nat) (H : SimpleGraph (fkSquareBoxPlanar n).V)
    {x y : FKIsingSquareWiredGadgetVertex n}
    (hxy : (fkIsingSquareLiftPhysicalGraph n H ⊔
      fkIsingSquareWiredExteriorGadget n).Adj x y) :
    (H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
      (fkIsingSquareWiredGadgetProjection n x)
      (fkIsingSquareWiredGadgetProjection n y) := by
  classical
  rcases hxy with hphysical | hgadget
  · rcases hphysical with ⟨u, v, rfl, rfl, huv⟩
    exact Adj.reachable (show
      (H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Adj u v from Or.inl huv)
  · rcases hgadget with ⟨v, hv, rfl, rfl⟩ | ⟨v, hv, rfl, rfl⟩
    · by_cases h : fkIsingSquareMarkedA n = v
      · subst v
        exact Reachable.refl _
      · exact Adj.reachable (show
          (H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Adj
            (fkIsingSquareMarkedA n) v from
        Or.inr ((boundaryCliqueGraph_adj
          (bdry := fkIsingSquareWiredArc n) _ _).2
            ⟨h, fkIsingSquareMarkedA_mem_wiredArc n, hv⟩))
    · by_cases h : v = fkIsingSquareMarkedA n
      · subst v
        exact Reachable.refl _
      · exact Adj.reachable (show
          (H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Adj
            v (fkIsingSquareMarkedA n) from
        Or.inr ((boundaryCliqueGraph_adj
          (bdry := fkIsingSquareWiredArc n) _ _).2
            ⟨h, hv, fkIsingSquareMarkedA_mem_wiredArc n⟩))


theorem fkIsingSquare_wiredExteriorGadget_reachable_iff_clique
    (n : Nat) (H : SimpleGraph (fkSquareBoxPlanar n).V)
    (x y : (fkSquareBoxPlanar n).V) :
    (fkIsingSquareLiftPhysicalGraph n H ⊔
        fkIsingSquareWiredExteriorGadget n).Reachable
        (.physical x) (.physical y) ↔
      (H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable x y := by
  classical
  constructor
  · intro h
    obtain ⟨p⟩ := h
    suffices hwalk : ∀ {u v : FKIsingSquareWiredGadgetVertex n},
        (fkIsingSquareLiftPhysicalGraph n H ⊔
          fkIsingSquareWiredExteriorGadget n).Walk u v →
        (H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
          (fkIsingSquareWiredGadgetProjection n u)
          (fkIsingSquareWiredGadgetProjection n v) by
      exact hwalk p
    intro u v q
    induction q with
    | nil => exact Reachable.refl _
    | cons huv q ih =>
        exact (fkIsingSquareWiredGadgetProjection_reachable n H huv).trans ih
  · intro h
    obtain ⟨p⟩ := h
    suffices hwalk : ∀ {u v : (fkSquareBoxPlanar n).V},
        (H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Walk u v →
        (fkIsingSquareLiftPhysicalGraph n H ⊔
          fkIsingSquareWiredExteriorGadget n).Reachable
            (.physical u) (.physical v) by
      exact hwalk p
    intro u v q
    induction q with
    | nil => exact Reachable.refl _
    | @cons u v w huv q ih =>
        have hstep : (fkIsingSquareLiftPhysicalGraph n H ⊔
            fkIsingSquareWiredExteriorGadget n).Reachable
              (.physical u) (.physical v) := by
          rcases huv with hH | hclique
          · exact Adj.reachable (show
                (fkIsingSquareLiftPhysicalGraph n H ⊔
                  fkIsingSquareWiredExteriorGadget n).Adj
                    (.physical u) (.physical v) by
              exact Or.inl ⟨u, v, rfl, rfl, hH⟩)
          · rw [boundaryCliqueGraph_adj] at hclique
            have hu : (fkIsingSquareWiredExteriorGadget n).Adj
                (.physical u) .exteriorRoot :=
              Or.inr ⟨u, hclique.2.1, rfl, rfl⟩
            have hv : (fkIsingSquareWiredExteriorGadget n).Adj
                (.exteriorRoot) (.physical v) :=
              Or.inl ⟨v, hclique.2.2, rfl, rfl⟩
            exact Adj.reachable (Or.inr hu) |>.trans (Adj.reachable (Or.inr hv))
        exact hstep.trans ih


end
end StatMech.Universality

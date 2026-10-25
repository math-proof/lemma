/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Def.StatisticalMechanics.Code.FK.EdgeSubsetDomainMarkov.Part4
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem openSub_edgeSubsetFibre_sup_frozen
    (K H B : SimpleGraph V) [DecidableRel K.Adj] (hKH : K ≤ H)
    (psi : ConfigSpace (Sym2 V)) (eta : ConfigSpace K.edgeSet) :
    openSub H (edgeSubsetFibreConfig K psi eta) ⊔ B =
      openSub K (extendActive K eta) ⊔
        edgeSubsetFrozenExteriorGraph K H B psi := by
  ext x y
  simp only [openSub_adj, SimpleGraph.sup_adj]
  constructor
  · rintro (⟨hH, hopen⟩ | hB)
    · by_cases hK : K.Adj x y
      · left
        refine ⟨hK, ?_⟩
        have he : s(x, y) ∈ K.edgeSet := by
          rw [SimpleGraph.mem_edgeSet]
          exact hK
        rw [extendActive_apply K eta ⟨s(x, y), he⟩]
        simpa [edgeSubsetFibreConfig, he] using hopen
      · right
        exact Or.inl ⟨hH, hK, by
          simpa [edgeSubsetFibreConfig,
            show s(x, y) ∉ K.edgeSet by
              rwa [SimpleGraph.mem_edgeSet]] using hopen⟩
    · exact Or.inr (Or.inr hB)
  · rintro (⟨hK, hopen⟩ | (hExt | hB))
    · left
      refine ⟨hKH hK, ?_⟩
      have he : s(x, y) ∈ K.edgeSet := by
        rw [SimpleGraph.mem_edgeSet]
        exact hK
      rw [edgeSubsetFibreConfig, dif_pos he]
      rw [extendActive_apply K eta ⟨s(x, y), he⟩] at hopen
      exact hopen
    · left
      refine ⟨hExt.1, ?_⟩
      have he : s(x, y) ∉ K.edgeSet := hExt.2.1
      simpa [edgeSubsetFibreConfig, he] using hExt.2.2
    · exact Or.inr hB

theorem reachable_of_adj_reachable
    {W : Type*} {A L : SimpleGraph W}
    (hstep : ∀ {x y}, A.Adj x y → L.Reachable x y)
    {x y : W} (hxy : A.Reachable x y) : L.Reachable x y := by
  obtain ⟨w⟩ := hxy
  induction w with
  | nil => exact .refl _
  | cons huv w ih => exact (hstep huv).trans ih

theorem sup_edgeSubsetFrozen_reachable_iff_induced
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    (psi : ConfigSpace (Sym2 V))
    (A : SimpleGraph V) (x y : V) :
    (A ⊔ edgeSubsetFrozenExteriorGraph K H B psi).Reachable x y ↔
      (A ⊔ edgeSubsetInducedWiring K H B psi).Reachable x y := by
  constructor
  · apply Reachable.mono
    intro u v huv
    rcases huv with hA | hE
    · exact Or.inl hA
    · exact Or.inr ⟨hE.ne, hE.reachable⟩
  · intro hxy
    apply reachable_of_adj_reachable (A :=
      A ⊔ edgeSubsetInducedWiring K H B psi) ?_ hxy
    intro u v huv
    rcases huv with hA | hC
    · exact (show (A ⊔ edgeSubsetFrozenExteriorGraph K H B psi).Adj u v
        from Or.inl hA).reachable
    · exact hC.2.mono le_sup_right

end
end StatMech.FK

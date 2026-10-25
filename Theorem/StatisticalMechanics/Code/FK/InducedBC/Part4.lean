/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.FK.BoxCrossGraph.Part19
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Instance.StatisticalMechanics.Code.FK.InducedBC.Part4
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


theorem psiExt_eq_false_of_range (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {e : Sym2 (boxVerts d (n+1))}
    (he : e ∈ Set.range (innerEdge d n)) :
    psiExt d n ψ ω e = psiExt d n (fun _ => false) ω e := by
  obtain ⟨e', rfl⟩ := he
  rw [psiExt_innerEdge, psiExt_innerEdge]


theorem psiWiredGraph_eq_sup (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    openSub (boxGraph d (n+1)) (psiExt d n ψ ω)
        ⊔ StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n+1))
      = innerImageGraph d n ω ⊔ outsideGraph d n ψ := by
  ext x y
  rw [SimpleGraph.sup_adj, openSub_adj, SimpleGraph.sup_adj, outsideGraph,
    SimpleGraph.sup_adj]
  constructor
  · rintro (⟨hadj, hopen⟩ | hclique)
    · by_cases hr : s(x, y) ∈ Set.range (innerEdge d n)
      · refine Or.inl ⟨hadj, ?_, hr⟩
        rw [← psiExt_eq_false_of_range d n ψ ω hr]; exact hopen
      · refine Or.inr (Or.inl ⟨hadj, ?_, hr⟩)
        rwa [psiExt_eq_psi_of_not_range d n ψ ω hr] at hopen
    · exact Or.inr (Or.inr hclique)
  · rintro (⟨hadj, hopen, hr⟩ | ⟨hadj, hopen, hr⟩ | hclique)
    · refine Or.inl ⟨hadj, ?_⟩
      rwa [psiExt_eq_false_of_range d n ψ ω hr]
    · refine Or.inl ⟨hadj, ?_⟩
      rwa [psiExt_eq_psi_of_not_range d n ψ ω hr]
    · exact Or.inr hclique


end FK
end StatMech

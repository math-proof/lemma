/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
import Theorem.StatisticalMechanics.Code.FK.Limits
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
import Instance.StatisticalMechanics.Code.FK.FreeWeakLimit
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK

variable {d : ℕ}


theorem inducedWiringFree_adj (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (x y : boxVerts d n) :
    (inducedWiringFree d n ψ).Adj x y
      ↔ x ≠ y ∧ (outsideOpenGraph d n ψ).Reachable (boxVertIncl d n x) (boxVertIncl d n y) :=
  Iff.rfl


theorem psiFreeGraph_eq_sup (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    openSub (boxGraph d (n+1)) (psiExt d n ψ ω)
      = innerImageGraph d n ω ⊔ outsideOpenGraph d n ψ := by
  ext x y
  rw [openSub_adj, SimpleGraph.sup_adj]
  constructor
  · rintro ⟨hadj, hopen⟩
    by_cases hr : s(x, y) ∈ Set.range (innerEdge d n)
    · refine Or.inl ⟨hadj, ?_, hr⟩
      rw [← psiExt_eq_false_of_range d n ψ ω hr]; exact hopen
    · refine Or.inr ⟨hadj, ?_, hr⟩
      rwa [psiExt_eq_psi_of_not_range d n ψ ω hr] at hopen
  · rintro (⟨hadj, hopen, hr⟩ | ⟨hadj, hopen, hr⟩)
    · refine ⟨hadj, ?_⟩
      rwa [psiExt_eq_false_of_range d n ψ ω hr]
    · refine ⟨hadj, ?_⟩
      rwa [psiExt_eq_psi_of_not_range d n ψ ω hr]


end FK
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc74disjointforest.Part2
import Theorem.StatisticalMechanics.Code.Percolation.OpenSpanningForestClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
import Def.StatisticalMechanics.Code.Walls.bc75spanningtree.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc75_spanForest_acyclic (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] :
    (bc75_spanForest ω L R c S).IsAcyclic :=
  osf_spanForest_acyclic (bc75_fiberQuotBox ω L R c S)


theorem bc75_spanForest_le (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)] :
    bc75_spanForest ω L R c S ≤ bc75_fiberQuotBox ω L R c S :=
  osf_spanForest_le (bc75_fiberQuotBox ω L R c S)


theorem bc75_spanForest_reachable_of (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) [Fintype (↑S : Type)]
    {u v : (↑S : Type)} (h : (bc75_fiberQuotBox ω L R c S).Reachable u v) :
    (bc75_spanForest ω L R c S).Reachable u v :=
  osf_spanForest_reachable_of (bc75_fiberQuotBox ω L R c S) h

open Classical in


theorem bc75_deg3_in_spanForest_of_gnCut (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) {y : Site d} {S : Set (Site d)} [Fintype (↑S : Type)]
    (hyS : y ∈ S) {v₁ v₂ v₃ : (↑S : Type)}
    (hadj₁ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS⟩ v₁)
    (hadj₂ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS⟩ v₂)
    (hadj₃ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS⟩ v₃)
    (hcut₁₂ : ¬ ((bc75_fiberQuotBox ω L R c S).induce
        ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
      ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₁).symm⟩
      ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₂).symm⟩)
    (hcut₁₃ : ¬ ((bc75_fiberQuotBox ω L R c S).induce
        ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
      ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₁).symm⟩
      ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₃).symm⟩)
    (hcut₂₃ : ¬ ((bc75_fiberQuotBox ω L R c S).induce
        ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
      ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₂).symm⟩
      ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₃).symm⟩) :
    3 ≤ (bc75_spanForest ω L R c S).degree ⟨y, hyS⟩ := by
  classical
  set F := bc75_spanForest ω L R c S with hF
  set Q := bc75_fiberQuotBox ω L R c S with hQ
  
  have hne₁ : (⟨y, hyS⟩ : (↑S : Type)) ≠ v₁ := Q.ne_of_adj hadj₁
  have hne₂ : (⟨y, hyS⟩ : (↑S : Type)) ≠ v₂ := Q.ne_of_adj hadj₂
  have hne₃ : (⟨y, hyS⟩ : (↑S : Type)) ≠ v₃ := Q.ne_of_adj hadj₃
  
  have hr₁ : F.Reachable ⟨y, hyS⟩ v₁ := bc75_spanForest_reachable_of ω L R c S hadj₁.reachable
  have hr₂ : F.Reachable ⟨y, hyS⟩ v₂ := bc75_spanForest_reachable_of ω L R c S hadj₂.reachable
  have hr₃ : F.Reachable ⟨y, hyS⟩ v₃ := bc75_spanForest_reachable_of ω L R c S hadj₃.reachable
  
  refine slh_deg_ge_three_of_cut hr₁ hr₂ hr₃ hne₁ hne₂ hne₃ ?_ ?_ ?_
  · intro hr; exact hcut₁₂ (hr.mono (fun a b hab => (bc75_spanForest_le ω L R c S) hab))
  · intro hr; exact hcut₁₃ (hr.mono (fun a b hab => (bc75_spanForest_le ω L R c S) hab))
  · intro hr; exact hcut₂₃ (hr.mono (fun a b hab => (bc75_spanForest_le ω L R c S) hab))


end StatMech.Walls

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/briraysintree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bcaconcreteclose
import Theorem.StatisticalMechanics.Code.Walls.bararmray
import Def.StatisticalMechanics.Code.Walls.briraysintree
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bri_rayGraph_le {V : Type*} (T : SimpleGraph V) (r : ℕ → V) (N : ℕ)
    (hadj : ∀ k, T.Adj (r k) (r (k + 1))) : bri_rayGraph r N ≤ T := by
  intro a b hab
  rw [bri_rayGraph, SimpleGraph.fromEdgeSet_adj] at hab
  obtain ⟨⟨k, hk, hek⟩, hne⟩ := hab
  rw [Sym2.eq_iff] at hek
  rcases hek with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hadj k
  · exact (hadj k).symm


theorem bri_rayGraph_acyclic {V : Type*} {T : SimpleGraph V} (hT : T.IsTree) (r : ℕ → V) (N : ℕ)
    (hadj : ∀ k, T.Adj (r k) (r (k + 1))) : (bri_rayGraph r N).IsAcyclic :=
  bau_isAcyclic_of_le_tree hT (bri_rayGraph_le T r N hadj)


theorem bri_union_le_acyclic {V : Type*} {T : SimpleGraph V} (hT : T.IsTree)
    {ι : Type*} (Gs : ι → SimpleGraph V) (hGs : ∀ i, Gs i ≤ T) :
    (⨆ i, Gs i).IsAcyclic :=
  bau_isAcyclic_of_le_tree hT (iSup_le hGs)


theorem bri_two_rays_acyclic {V : Type*} {T : SimpleGraph V} (hT : T.IsTree) (r s : ℕ → V) (N M : ℕ)
    (hr : ∀ k, T.Adj (r k) (r (k + 1))) (hs : ∀ k, T.Adj (s k) (s (k + 1))) :
    (bri_rayGraph r N ⊔ bri_rayGraph s M).IsAcyclic :=
  bau_isAcyclic_of_le_tree hT (sup_le (bri_rayGraph_le T r N hr) (bri_rayGraph_le T s M hs))


end StatMech.Walls

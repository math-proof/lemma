/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Def.StatisticalMechanics.Code.FK.TranslationInvariance.Part2
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace


variable {V : Type*} [Fintype V] [DecidableEq V]


variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem fkTI_numClusters_reCfg (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (ω : ConfigSpace (Sym2 V)) :
    numClusters G (reCfg σ ω) = numClusters G ω := by
  unfold numClusters
  exact Fintype.card_congr (fkTI_openSubIso G σ hσ ω).connectedComponentEquiv


omit [DecidableEq V] in

theorem fkTI_mem_edgeFinset_map (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    Sym2.map σ e ∈ G.edgeFinset := by
  induction e using Sym2.ind with | _ a b =>
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
  rw [Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hσ]
  exact he

omit [DecidableEq V] in

theorem fkTI_mem_edgeFinset_map_symm (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    Sym2.map σ.symm e ∈ G.edgeFinset := by
  induction e using Sym2.ind with | _ a b =>
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
  rw [Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  rw [← hσ]; simpa using he


theorem fkTI_edgeProduct_reCfg (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    edgeProduct G p (reCfg σ ω) = edgeProduct G p ω := by
  unfold edgeProduct reCfg
  apply Finset.prod_bij' (i := fun e _ => Sym2.map σ e) (j := fun e _ => Sym2.map σ.symm e)
  · intro a ha; exact fkTI_mem_edgeFinset_map G σ hσ ha
  · intro a ha; exact fkTI_mem_edgeFinset_map_symm G σ hσ ha
  · intro a ha; rw [Sym2.map_map]; simp
  · intro a ha; rw [Sym2.map_map]; simp
  · intro a ha; rfl


theorem fkTI_fkWeight_reCfg (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (p q : ℝ) (ω : ConfigSpace (Sym2 V)) :
    fkWeight G p q (reCfg σ ω) = fkWeight G p q ω := by
  unfold fkWeight
  rw [fkTI_edgeProduct_reCfg G σ hσ p ω, fkTI_numClusters_reCfg G σ hσ ω]


theorem fkTI_fkZ_reCfg (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (p q : ℝ) :
    fkZ G p q = ∑ ω : ConfigSpace (Sym2 V), fkWeight G p q (reCfg σ ω) := by
  unfold fkZ
  exact Finset.sum_congr rfl fun ω _ => (fkTI_fkWeight_reCfg G σ hσ p q ω).symm


theorem fkTI_fkProb_reCfg (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (p q : ℝ) (ω : ConfigSpace (Sym2 V)) :
    fkProb G p q (reCfg σ ω) = fkProb G p q ω := by
  unfold fkProb
  rw [fkTI_fkWeight_reCfg G σ hσ p q ω]


end FK
end StatMech

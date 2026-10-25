/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Def.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part2
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace


variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


variable (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]


theorem fvs_numClusters_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (ω : ConfigSpace (Sym2 W)) :
    numClusters G (reCfgIso σ ω) = numClusters H ω := by
  unfold numClusters
  exact Fintype.card_congr (fvs_openSubIso G H σ hσ ω).connectedComponentEquiv


omit [DecidableEq V] [DecidableEq W] in

theorem fvs_mem_edgeFinset_map (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    Sym2.map σ e ∈ H.edgeFinset := by
  induction e using Sym2.ind with | _ a b =>
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
  rw [Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, ← hσ]
  exact he

omit [DecidableEq V] [DecidableEq W] in

theorem fvs_mem_edgeFinset_map_symm (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) {e : Sym2 W} (he : e ∈ H.edgeFinset) :
    Sym2.map σ.symm e ∈ G.edgeFinset := by
  induction e using Sym2.ind with | _ a b =>
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
  rw [Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hσ]
  simpa using he


theorem fvs_edgeProduct_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (p : ℝ) (ω : ConfigSpace (Sym2 W)) :
    edgeProduct G p (reCfgIso σ ω) = edgeProduct H p ω := by
  unfold edgeProduct reCfgIso
  symm
  apply Finset.prod_bij' (i := fun e _ => Sym2.map σ.symm e) (j := fun e _ => Sym2.map σ e)
  · intro a ha; exact fvs_mem_edgeFinset_map_symm G H σ hσ ha
  · intro a ha; exact fvs_mem_edgeFinset_map G H σ hσ ha
  · intro a ha; rw [Sym2.map_map]; simp
  · intro a ha; rw [Sym2.map_map]; simp
  · intro a ha; rw [Sym2.map_map]; simp


theorem fvs_fkWeight_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (p q : ℝ) (ω : ConfigSpace (Sym2 W)) :
    fkWeight G p q (reCfgIso σ ω) = fkWeight H p q ω := by
  unfold fkWeight
  rw [fvs_edgeProduct_reCfgIso G H σ hσ p ω, fvs_numClusters_reCfgIso G H σ hσ ω]


theorem fvs_fkZ_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (p q : ℝ) :
    fkZ G p q = fkZ H p q := by
  unfold fkZ
  rw [← Equiv.sum_comp (reCfgIsoEquiv σ) (fun ω => fkWeight G p q ω)]
  exact Finset.sum_congr rfl fun ω _ => fvs_fkWeight_reCfgIso G H σ hσ p q ω


theorem fvs_fkProb_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (p q : ℝ) (ω : ConfigSpace (Sym2 W)) :
    fkProb G p q (reCfgIso σ ω) = fkProb H p q ω := by
  unfold fkProb
  rw [fvs_fkWeight_reCfgIso G H σ hσ p q ω, fvs_fkZ_reCfgIso G H σ hσ p q]


end FK
end StatMech

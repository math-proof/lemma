/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Def.StatisticalMechanics.Code.FK.TranslationInvariance.Part3
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


variable (bdry : V → Prop) [DecidablePred bdry]


theorem fkTI_numClustersWired_reCfg (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (hbdry : ∀ x, bdry (σ x) ↔ bdry x)
    (ω : ConfigSpace (Sym2 V)) :
    StatMech.Lattice.numClustersWired G bdry (reCfg σ ω)
      = StatMech.Lattice.numClustersWired G bdry ω := by
  unfold StatMech.Lattice.numClustersWired
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (fkTI_wiredGraphIso G bdry σ hσ hbdry ω).connectedComponentEquiv


theorem fkTI_wiredFkWeight_reCfg (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (hbdry : ∀ x, bdry (σ x) ↔ bdry x)
    (p q : ℝ) (ω : ConfigSpace (Sym2 V)) :
    wiredFkWeight G bdry p q (reCfg σ ω) = wiredFkWeight G bdry p q ω := by
  unfold wiredFkWeight
  rw [fkTI_edgeProduct_reCfg G σ hσ p ω, fkTI_numClustersWired_reCfg G bdry σ hσ hbdry ω]


theorem fkTI_wiredFkProb_reCfg (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (hbdry : ∀ x, bdry (σ x) ↔ bdry x)
    (p q : ℝ) (ω : ConfigSpace (Sym2 V)) :
    wiredFkProb G bdry p q (reCfg σ ω) = wiredFkProb G bdry p q ω := by
  unfold wiredFkProb
  rw [fkTI_wiredFkWeight_reCfg G bdry σ hσ hbdry p q ω]


theorem fkTI_edgeMargProb_reCfg_inv (σ : V ≃ V) (μ : ConfigSpace (Sym2 V) → ℝ)
    (hμ : ∀ ω, μ (reCfg σ.symm ω) = μ ω) (e : Sym2 V) :
    edgeMargProb μ (Sym2.map σ e) = edgeMargProb μ e := by
  unfold edgeMargProb
  rw [← Equiv.sum_comp (reCfgEquiv σ.symm)
    (fun ω => (if ω (Sym2.map σ e) then (1:ℝ) else 0) * μ ω)]
  apply Finset.sum_congr rfl
  intro ω _
  show (if (reCfg σ.symm ω) (Sym2.map σ e) then (1:ℝ) else 0) * μ (reCfg σ.symm ω) = _
  have h1 : (reCfg σ.symm ω) (Sym2.map σ e) = ω e := by
    unfold reCfg; rw [Sym2.map_map]; simp
  rw [h1, hμ ω]


theorem fkTI_edgeMargProb_fkProb_reCfg (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (p q : ℝ) (e : Sym2 V) :
    edgeMargProb (fkProb G p q) (Sym2.map σ e) = edgeMargProb (fkProb G p q) e := by
  refine fkTI_edgeMargProb_reCfg_inv σ (fkProb G p q) (fun ω => ?_) e
  exact fkTI_fkProb_reCfg G σ.symm (fun x y => by
    rw [← hσ (σ.symm x) (σ.symm y)]; simp) p q ω


theorem fkTI_edgeMargProb_wiredFkProb_reCfg (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (hbdry : ∀ x, bdry (σ x) ↔ bdry x)
    (p q : ℝ) (e : Sym2 V) :
    edgeMargProb (wiredFkProb G bdry p q) (Sym2.map σ e)
      = edgeMargProb (wiredFkProb G bdry p q) e := by
  refine fkTI_edgeMargProb_reCfg_inv σ (wiredFkProb G bdry p q) (fun ω => ?_) e
  refine fkTI_wiredFkProb_reCfg G bdry σ.symm (fun x y => by
    rw [← hσ (σ.symm x) (σ.symm y)]; simp) (fun x => by rw [← hbdry (σ.symm x)]; simp) p q ω

end FK
end StatMech

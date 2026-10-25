/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Def.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part3
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


variable (bdryV : V → Prop) [DecidablePred bdryV] (bdryW : W → Prop) [DecidablePred bdryW]


theorem fvs_numClustersWired_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (hbdry : ∀ x, bdryV x ↔ bdryW (σ x))
    (ω : ConfigSpace (Sym2 W)) :
    StatMech.Lattice.numClustersWired G bdryV (reCfgIso σ ω)
      = StatMech.Lattice.numClustersWired H bdryW ω := by
  unfold StatMech.Lattice.numClustersWired
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (fvs_wiredGraphIso G H bdryV bdryW σ hσ hbdry ω).connectedComponentEquiv


theorem fvs_wiredFkWeight_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (hbdry : ∀ x, bdryV x ↔ bdryW (σ x))
    (p q : ℝ) (ω : ConfigSpace (Sym2 W)) :
    wiredFkWeight G bdryV p q (reCfgIso σ ω) = wiredFkWeight H bdryW p q ω := by
  unfold wiredFkWeight
  rw [fvs_edgeProduct_reCfgIso G H σ hσ p ω,
    fvs_numClustersWired_reCfgIso G H bdryV bdryW σ hσ hbdry ω]


theorem fvs_wiredFkZ_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (hbdry : ∀ x, bdryV x ↔ bdryW (σ x))
    (p q : ℝ) :
    wiredFkZ G bdryV p q = wiredFkZ H bdryW p q := by
  unfold wiredFkZ
  rw [← Equiv.sum_comp (reCfgIsoEquiv σ) (fun ω => wiredFkWeight G bdryV p q ω)]
  exact Finset.sum_congr rfl fun ω _ => fvs_wiredFkWeight_reCfgIso G H bdryV bdryW σ hσ hbdry p q ω


theorem fvs_wiredFkProb_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (hbdry : ∀ x, bdryV x ↔ bdryW (σ x))
    (p q : ℝ) (ω : ConfigSpace (Sym2 W)) :
    wiredFkProb G bdryV p q (reCfgIso σ ω) = wiredFkProb H bdryW p q ω := by
  unfold wiredFkProb
  rw [fvs_wiredFkWeight_reCfgIso G H bdryV bdryW σ hσ hbdry p q ω,
    fvs_wiredFkZ_reCfgIso G H bdryV bdryW σ hσ hbdry p q]


theorem fvs_edgeMargProb_reCfgIso_inv (σ : V ≃ W)
    (μV : ConfigSpace (Sym2 V) → ℝ) (μW : ConfigSpace (Sym2 W) → ℝ)
    (hμ : ∀ ω, μV (reCfgIso σ ω) = μW ω) (e : Sym2 V) :
    edgeMargProb μW (Sym2.map σ e) = edgeMargProb μV e := by
  unfold edgeMargProb
  rw [← Equiv.sum_comp (reCfgIsoEquiv σ).symm
    (fun ω => (if ω (Sym2.map σ e) then (1:ℝ) else 0) * μW ω)]
  apply Finset.sum_congr rfl
  intro ω _
  show (if ((reCfgIsoEquiv σ).symm ω) (Sym2.map σ e) then (1:ℝ) else 0)
      * μW ((reCfgIsoEquiv σ).symm ω) = _
  have hsymm : (reCfgIsoEquiv σ).symm ω = reCfgIso σ.symm ω := rfl
  rw [hsymm]
  have h1 : (reCfgIso σ.symm ω) (Sym2.map σ e) = ω e := by
    unfold reCfgIso; rw [Sym2.map_map]; simp
  rw [h1]
  have h2 : μW (reCfgIso σ.symm ω) = μV ω := by
    have := hμ (reCfgIso σ.symm ω)
    rw [fvs_reCfgIso_reCfgIso' σ ω] at this
    exact this.symm
  rw [h2]


theorem fvs_edgeMargProb_fkProb_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (p q : ℝ) (e : Sym2 V) :
    edgeMargProb (fkProb H p q) (Sym2.map σ e) = edgeMargProb (fkProb G p q) e :=
  fvs_edgeMargProb_reCfgIso_inv σ (fkProb G p q) (fkProb H p q)
    (fun ω => fvs_fkProb_reCfgIso G H σ hσ p q ω) e


theorem fvs_edgeMargProb_wiredFkProb_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (hbdry : ∀ x, bdryV x ↔ bdryW (σ x))
    (p q : ℝ) (e : Sym2 V) :
    edgeMargProb (wiredFkProb H bdryW p q) (Sym2.map σ e)
      = edgeMargProb (wiredFkProb G bdryV p q) e :=
  fvs_edgeMargProb_reCfgIso_inv σ (wiredFkProb G bdryV p q) (wiredFkProb H bdryW p q)
    (fun ω => fvs_wiredFkProb_reCfgIso G H bdryV bdryW σ hσ hbdry p q ω) e


theorem fvs_finiteVolume_shift_invariant (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (hbdry : ∀ x, bdryV x ↔ bdryW (σ x))
    (p q : ℝ) (e : Sym2 V) :
    edgeMargProb (wiredFkProb H bdryW p q) (Sym2.map σ e)
        = edgeMargProb (wiredFkProb G bdryV p q) e
      ∧ edgeMargProb (fkProb H p q) (Sym2.map σ e) = edgeMargProb (fkProb G p q) e :=
  ⟨fvs_edgeMargProb_wiredFkProb_reCfgIso G H bdryV bdryW σ hσ hbdry p q e,
    fvs_edgeMargProb_fkProb_reCfgIso G H σ hσ p q e⟩

end FK
end StatMech

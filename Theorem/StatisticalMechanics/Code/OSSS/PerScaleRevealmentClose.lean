/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PerScaleRevealmentClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.PrefixCoversClose.Part3
import Theorem.StatisticalMechanics.Code.OSSS.FKRevealmentClose
open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace PerScaleRevealmentClose

open OSSS.Coding

open OSSS.AdaptMConditional

open StatMech.OSSS

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.ReachBoxCrossing

open StatMech.OSSS.ReachDomination

open StatMech.OSSS.RevealmentBoxCrossing

open StatMech.OSSS.PrefixCoversClose

open StatMech.OSSS.FKRevealmentClose

open StatMech.OSSS.MonotonicFK

open StatMech.Lattice

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {V : Type*} [DecidableEq V]


theorem psr_frontierConn_first_iff {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (endU endV : E → V) (B : Set V) {e₀ : E} (he₀ : (σ.symm e₀ : ℕ) = 0) :
    FrontierConn σ f endU endV B e₀ ↔
      ∀ X : ConfigSpace E, (∃ w, f w ≠ f X) →
        ConnOpenSet endU endV X (endU e₀) B ∨ ConnOpenSet endU endV X (endV e₀) B := by
  unfold FrontierConn
  rw [he₀]
  have hpref : prefixSet (σ : Fin n → E) 0 = ∅ := prefixSet_zero _
  constructor
  · intro h X ⟨w, hw⟩
    refine h X (fun hdet => hw ?_)
    exact hdet w (by rw [hpref]; intro a ha; simp at ha)
  · intro h X hnotdet
    refine h X ?_
    by_contra hcon
    rw [not_exists] at hcon
    push Not at hcon
    exact hnotdet (fun w _ => hcon w)


theorem psr_frontierConn_first_refutable {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (endU endV : E → V) (B : Set V) {e₀ : E} (he₀ : (σ.symm e₀ : ℕ) = 0)
    (X : ConfigSpace E) (hnc : ∃ w, f w ≠ f X)
    (hnotU : ¬ ConnOpenSet endU endV X (endU e₀) B)
    (hnotV : ¬ ConnOpenSet endU endV X (endV e₀) B) :
    ¬ FrontierConn σ f endU endV B e₀ := by
  rw [psr_frontierConn_first_iff σ f endU endV B he₀]
  intro h
  rcases h X hnc with hU | hV
  · exact hnotU hU
  · exact hnotV hV


theorem psr_revealAdapt_first_gt {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) {e₀ : E}
    (he₀ : (σ.symm e₀ : ℕ) = 0) (hnc : ∀ X, ¬ ∀ w, f w = f X) {c : ℝ} (hc : c < 1) :
    ¬ revealAdapt μ σ f e₀ ≤ c :=
  FKRevealmentClose.revealAdapt_single_no_over_n hpos hμ1 σ f e₀ he₀ hnc hc


theorem psr_frontierConn_first_refutable_witness {n : ℕ} (σ : Fin n ≃ E)
    (endU endV : E → V) (B C : Set V) {e₀ : E} (he₀ : (σ.symm e₀ : ℕ) = 0)
    (X w : ConfigSpace E)
    (hX0 : ¬ ∃ x ∈ C, ConnOpenSet endU endV X x B)
    (hw1 : ∃ x ∈ C, ConnOpenSet endU endV w x B)
    (hnotU : ¬ ConnOpenSet endU endV X (endU e₀) B)
    (hnotV : ¬ ConnOpenSet endU endV X (endV e₀) B) :
    ¬ FrontierConn σ (indicatorConn endU endV B C) endU endV B e₀ := by
  refine psr_frontierConn_first_refutable σ _ endU endV B he₀ X ?_ hnotU hnotV
  refine ⟨w, ?_⟩
  unfold indicatorConn
  rw [if_pos hw1, if_neg hX0]
  norm_num


section Lattice

variable {d : ℕ}


theorem psr_revealAdapt_le_connBox_of_pos {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {nE : ℕ} (σ : Fin nE ≃ E)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (k n : ℕ)
    (hσ : ∀ e' : E, (TopIncident endU endV (vertexBoundary d k) e' ↔
        (σ.symm e' : ℕ) <
          (Finset.univ.filter (TopIncident endU endV (vertexBoundary d k))).card))
    (e : E)
    (he : (Finset.univ.filter (TopIncident endU endV (vertexBoundary d k))).card - 1
        ≤ (σ.symm e : ℕ))
    [DecidablePred (fun X => ConnOpenSet endU endV X (endU e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnOpenSet endU endV X (endV e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k))] :
    revealAdapt μ σ (indicatorConn endU endV (vertexBoundary d k) (vertexBoundary d n)) e
      ≤ Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k)
                    then (1 : ℝ) else 0)
        + Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k)
                    then (1 : ℝ) else 0) := by
  have hfront : FrontierConn σ
      (indicatorConn endU endV (vertexBoundary d k) (vertexBoundary d n))
      endU endV (vertexBoundary d k) e :=
    frontierConn_of_clusterMeasurable σ endU endV (vertexBoundary d k) e
      (clusterMeasurable_indicatorConn endU endV (vertexBoundary d k) (vertexBoundary d n))
      (prefixCoversCluster_clusterOrder σ endU endV (vertexBoundary d k) hσ e he)
  exact revealAdapt_le_connBox hpos hμ1 σ
    (indicatorConn endU endV (vertexBoundary d k) (vertexBoundary d n))
    hinj hcoh hadj k e hfront


theorem psr_revealAdapt_le_connBox_frontier {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (k n : ℕ) (nE : ℕ) (hnE : Fintype.card E = nE)
    (hne : (Finset.univ.filter (TopIncident endU endV (vertexBoundary d k))).Nonempty) :
    ∃ (σ : Fin nE ≃ E) (e : E),
      TopIncident endU endV (vertexBoundary d k) e ∧
      revealAdapt μ σ (indicatorConn endU endV (vertexBoundary d k) (vertexBoundary d n)) e
        ≤ Lindeberg.mean μ
            (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k)
                      then (1 : ℝ) else 0)
          + Lindeberg.mean μ
            (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k)
                      then (1 : ℝ) else 0) := by
  classical
  obtain ⟨σ, hσ⟩ := clusterOrder_exists (TopIncident endU endV (vertexBoundary d k)) nE hnE
  have hm1 : 1 ≤ (Finset.univ.filter (TopIncident endU endV (vertexBoundary d k))).card :=
    Finset.Nonempty.card_pos hne
  have hmn : (Finset.univ.filter (TopIncident endU endV (vertexBoundary d k))).card ≤ nE := by
    rw [← hnE, ← Finset.card_univ]; exact Finset.card_filter_le _ _
  set e : E := σ ⟨(Finset.univ.filter (TopIncident endU endV (vertexBoundary d k))).card - 1,
      by omega⟩ with hedef
  have hsymm : (σ.symm e : ℕ) =
      (Finset.univ.filter (TopIncident endU endV (vertexBoundary d k))).card - 1 := by
    rw [hedef, Equiv.symm_apply_apply]
  have htop : TopIncident endU endV (vertexBoundary d k) e := by rw [hσ e, hsymm]; omega
  refine ⟨σ, e, htop, ?_⟩
  exact psr_revealAdapt_le_connBox_of_pos hpos hμ1 σ hinj hcoh hadj k n hσ e (by rw [hsymm])

end Lattice
end PerScaleRevealmentClose
end OSSS
end StatMech

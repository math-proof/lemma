/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.RevealmentCrossBox.Part7
import Theorem.StatisticalMechanics.Code.OSSS.SharpnessFK
import Theorem.StatisticalMechanics.Code.Walls.oc_boxcrossingscalesum
import Theorem.StatisticalMechanics.Code.Walls.oc_boxobjects.Part2
import Def.StatisticalMechanics.Code.Walls.oc_core.Part2
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.DecisionTree

open StatMech.OSSS.Revealment

open StatMech.OSSS.RevealmentConstruction

open StatMech.Lattice

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]


section Headline

variable {d : ℕ}


theorem oc_scaleSum_le {ν : E → Bool → ℝ} (edge : E → Sym2 (Site d))
    (endU endV : E → Site d) (n : ℕ)
    (μTrans : Site d → ℕ → ℝ) (hμ : ∀ x j, 0 ≤ μTrans x j)
    (Λ : Finset (Site d)) (hΛne : Λ.Nonempty)
    (rdist : Site d → ℕ) (e : E)
    (hru : endU e ∈ Λ) (hrv : endV e ∈ Λ)
    (hruN : rdist (endU e) ≤ n) (hrvN : rdist (endV e) ≤ n)
    (hcompu : ∀ k,
      (expect ν fun ω =>
          if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0)
        ≤ μTrans (endU e) ((k : ℤ) - (rdist (endU e) : ℤ)).natAbs)
    (hcompv : ∀ k,
      (expect ν fun ω =>
          if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0)
        ≤ μTrans (endV e) ((k : ℤ) - (rdist (endV e) : ℤ)).natAbs) :
    (∑ k : oc_ScaleIdx n, oc_Rscale (ν := ν) edge endU endV n k e)
      ≤ 4 * Λ.sup' hΛne (fun x => ∑ j ∈ Finset.range (n + 1), μTrans x j) := by
  
  have hreindex : (∑ k : oc_ScaleIdx n, oc_Rscale (ν := ν) edge endU endV n k e)
      = ∑ k ∈ Finset.Icc 1 n,
          ((expect ν fun ω =>
              if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0)
            + (expect ν fun ω =>
                if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k)
                then (1 : ℝ) else 0)) := by
    simp only [oc_Rscale]
    exact Finset.sum_coe_sort (Finset.Icc 1 n)
      (fun k => (expect ν fun ω =>
          if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0)
        + (expect ν fun ω =>
            if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0))
  rw [hreindex]
  exact oc_box_crossing_scale_sum Λ hΛne μTrans hμ n (rdist (endU e)) (rdist (endV e))
    hruN hrvN (endU e) (endV e) hru hrv
    (fun k => expect ν fun ω =>
      if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0)
    (fun k => expect ν fun ω =>
      if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0)
    hcompu hcompv


theorem oc_corOSSS {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (n : ℕ) (hn : 1 ≤ n) (l : List E)
    (discF : ℕ → Finset (Site d))
    (hdisc : ∀ k, ∀ x ∈ discF k, x ∈ vertexBoundary d k)
    (hT : ∀ k : oc_ScaleIdx n,
      (oc_clusterTree endU endV o n l discF k.1).evalR = A.indicator (fun _ => (1 : ℝ)))
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
    (μTrans : Site d → ℕ → ℝ) (hμ : ∀ x j, 0 ≤ μTrans x j)
    (Λ : Finset (Site d)) (hΛne : Λ.Nonempty)
    (rdist : Site d → ℕ)
    (hru : ∀ e, endU e ∈ Λ) (hrv : ∀ e, endV e ∈ Λ)
    (hruN : ∀ e, rdist (endU e) ≤ n) (hrvN : ∀ e, rdist (endV e) ≤ n)
    (hcompu : ∀ e k,
      (expect ν fun ω =>
          if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0)
        ≤ μTrans (endU e) ((k : ℤ) - (rdist (endU e) : ℤ)).natAbs)
    (hcompv : ∀ e k,
      (expect ν fun ω =>
          if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0)
        ≤ μTrans (endV e) ((k : ℤ) - (rdist (endV e) : ℤ)).natAbs) :
    (Fintype.card (oc_ScaleIdx n) : ℝ) * c₀
        * (expect ν (A.indicator (fun _ => (1 : ℝ)))
            * (1 - expect ν (A.indicator (fun _ => (1 : ℝ)))))
      ≤ (4 * Λ.sup' hΛne (fun x => ∑ j ∈ Finset.range (n + 1), μTrans x j))
          * ∑ e, cov ν (CovLowerBound.coordI e) (A.indicator (fun _ => (1 : ℝ))) := by
  haveI : Nonempty (oc_ScaleIdx n) := ⟨⟨1, by simp [Finset.mem_Icc]; omega⟩⟩
  refine oc_familyAveraged_covLowerBound hν hA
    (fun k => oc_clusterTree endU endV o n l discF k.1) hT
    (fun k e => oc_Rscale (ν := ν) edge endU endV n k e) ?_ c₀ hc₀nn hc₀
    (4 * Λ.sup' hΛne (fun x => ∑ j ∈ Finset.range (n + 1), μTrans x j)) ?_ ?_
  · 
    intro k e
    exact oc_perScaleRevealment hν hinj hcoh hadj o n l discF hdisc k.1 e
  · 
    have hsup : 0 ≤ Λ.sup' hΛne (fun x => ∑ j ∈ Finset.range (n + 1), μTrans x j) := by
      obtain ⟨x, hx⟩ := hΛne
      exact le_trans (Finset.sum_nonneg (fun j _ => hμ x j))
        (Finset.le_sup' (fun x => ∑ j ∈ Finset.range (n + 1), μTrans x j) hx)
    positivity
  · 
    intro e
    exact oc_scaleSum_le edge endU endV n μTrans hμ Λ hΛne rdist e
      (hru e) (hrv e) (hruN e) (hrvN e) (hcompu e) (hcompv e)

end Headline


section SharpForm

variable {d : ℕ}


theorem oc_sharp_covLowerBound {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (T : κ → DecisionTree E) (hT : ∀ k, (T k).evalR = A.indicator (fun _ => (1 : ℝ)))
    (R : κ → E → ℝ) (hreach : ∀ k e, reveal ν (T k) e ≤ R k e)
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
    (D Sn : ℝ) (hDnn : 0 ≤ D) (hsum : ∀ e, (∑ k, R k e) ≤ D)
    (hDS : D ≤ 8 * Sn)
    (hcovnn : 0 ≤ ∑ e, cov ν (CovLowerBound.coordI e) (A.indicator (fun _ => (1 : ℝ)))) :
    (Fintype.card κ : ℝ) * c₀
        * (expect ν (A.indicator (fun _ => (1 : ℝ)))
            * (1 - expect ν (A.indicator (fun _ => (1 : ℝ)))))
      ≤ (8 * Sn) * ∑ e, cov ν (CovLowerBound.coordI e) (A.indicator (fun _ => (1 : ℝ))) := by
  refine le_trans (oc_familyAveraged_covLowerBound hν hA T hT R hreach c₀ hc₀nn hc₀ D hDnn hsum)
    ?_
  exact mul_le_mul_of_nonneg_right hDS hcovnn


theorem oc_fourD_le_eight_S {V : Type*} [Fintype V] [DecidableEq V]
    (Gf : ℕ → SimpleGraph V) [∀ n, DecidableRel (Gf n).Adj]
    (Af : ℕ → Set (ConfigSpace (Sym2 V))) (n : ℕ) (β : ℝ)
    (D : ℝ) (hD : D ≤ 2 * oc_S Gf Af n β) :
    4 * D ≤ 8 * oc_S Gf Af n β := by
  linarith

end SharpForm
end Walls
end StatMech

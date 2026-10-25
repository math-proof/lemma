/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachDomination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.ReachBoxCrossing.Part2
import Def.StatisticalMechanics.Code.OSSS.ReachDomination.Part3
open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace ReachDomination

open OSSS.Monotonic OSSS.AdaptMConditional StatMech.Probability

open StatMech.OSSS.MonotonicFK

open StatMech.OSSS.AdaptDisintegration

open OSSS.GrandCoupling OSSS.Coding

open StatMech.OSSS.RevealmentBoundAssembly

open StatMech.OSSS.RevealmentBoxCrossing

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.ReachBoxCrossing

open StatMech.Lattice

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {V : Type*} [DecidableEq V]


omit [Fintype E] in


theorem detAtC_of_not_incident {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (endU endV : E → V) (B : Set V) (e : E) (X : ConfigSpace E)
    (hfmeas : ClusterMeasurable f endU endV B)
    (hcover : PrefixCoversCluster σ endU endV B e)
    (hnotincid : ¬ IncidentCluster endU endV X B e) :
    detAtC (σ : Fin n → E) f X (σ.symm e : ℕ) := by
  intro w hw
  
  refine hfmeas X w (fun e' hincid => ?_)
  
  
  by_cases he' : e' = e
  · exact absurd (he' ▸ hincid) hnotincid
  · exact hw e' (hcover X e' he' hincid)

omit [Fintype E] in


theorem frontierConn_of_clusterMeasurable {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (endU endV : E → V) (B : Set V) (e : E)
    (hfmeas : ClusterMeasurable f endU endV B)
    (hcover : PrefixCoversCluster σ endU endV B e) :
    FrontierConn σ f endU endV B e := by
  intro X hnotdet
  
  
  by_contra hcon
  exact hnotdet (detAtC_of_not_incident σ endU endV B e X hfmeas hcover hcon)


section Lattice

variable {d : ℕ}


theorem reachProb_le_connBox_of_clusterMeasurable {μ : ConfigSpace E → ℝ}
    (hμ0 : ∀ ω, 0 ≤ μ ω)
    {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (k : ℕ) (e : E)
    (hfmeas : ClusterMeasurable f endU endV (vertexBoundary d k))
    (hcover : PrefixCoversCluster σ endU endV (vertexBoundary d k) e)
    [DecidablePred (fun X => ConnOpenSet endU endV X (endU e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnOpenSet endU endV X (endV e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k))] :
    reachProb μ σ f e
      ≤ Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k)
                    then (1 : ℝ) else 0)
        + Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k)
                    then (1 : ℝ) else 0) :=
  reachProb_le_connBox hμ0 σ f hinj hcoh hadj k e
    (frontierConn_of_clusterMeasurable σ endU endV (vertexBoundary d k) e hfmeas hcover)


theorem os_cov_lower_bound_from_clusterMeasurable {μ : ConfigSpace E → ℝ}
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ)
    (hmono : IsMonotonicMeasure μ)
    {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f)
    (hf1 : ∀ ω, f ω ≤ 1) (hidem : ∀ ω, f ω * f ω = f ω)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (k : ℕ) (D : ℝ) (hDpos : 0 < D)
    [∀ e X, Decidable (ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k))]
    [∀ e X, Decidable (ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k))]
    [∀ e X, Decidable (ConnOpenSet endU endV X (endU e) (vertexBoundary d k))]
    [∀ e X, Decidable (ConnOpenSet endU endV X (endV e) (vertexBoundary d k))]
    (hfmeas : ClusterMeasurable f endU endV (vertexBoundary d k))
    (hcover : ∀ e, PrefixCoversCluster σ endU endV (vertexBoundary d k) e)
    (hbox : ∀ e,
      Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k)
                    then (1 : ℝ) else 0)
        + Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k)
                    then (1 : ℝ) else 0) ≤ D) :
    Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) / D
      ≤ ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) :=
  os_cov_lower_bound_from_box_crossing hpos hμ1 hFKG hmono σ hf hf0 hf1 hidem
    hinj hcoh hadj k D hDpos
    (fun e => frontierConn_of_clusterMeasurable σ endU endV (vertexBoundary d k) e
      hfmeas (hcover e))
    hbox

end Lattice


theorem prefixCoversCluster_of_prefix_cofinite {n : ℕ} (σ : Fin n ≃ E) (endU endV : E → V)
    (B : Set V) (e : E)
    (hcofin : ∀ e' : E, e' ≠ e → e' ∈ prefixSet (σ : Fin n → E) (σ.symm e : ℕ)) :
    PrefixCoversCluster σ endU endV B e :=
  fun _ e' he' _ => hcofin e' he'


theorem prefix_cofinite_of_last {n : ℕ} (hn : 1 ≤ n) (σ : Fin n ≃ E)
    {e : E} (he : (σ.symm e : ℕ) = n - 1) :
    ∀ e' : E, e' ≠ e → e' ∈ prefixSet (σ : Fin n → E) (σ.symm e : ℕ) := by
  intro e' he'
  rw [mem_prefixSet_iff]
  refine ⟨σ.symm e', ?_, by simp⟩
  
  have hne : (σ.symm e' : Fin n) ≠ σ.symm e := fun h => he' (by
    have := congrArg σ h; simpa using this)
  have hval : (σ.symm e' : ℕ) ≠ (σ.symm e : ℕ) := fun h => hne (Fin.ext h)
  have hlt : (σ.symm e' : ℕ) < n := (σ.symm e').2
  rw [he]; omega


theorem frontierConn_indicatorConn_last {n : ℕ} (hn : 1 ≤ n) (σ : Fin n ≃ E)
    (endU endV : E → V) (B C : Set V) {e : E} (he : (σ.symm e : ℕ) = n - 1) :
    FrontierConn σ (indicatorConn endU endV B C) endU endV B e :=
  frontierConn_of_clusterMeasurable σ endU endV B e
    (clusterMeasurable_indicatorConn endU endV B C)
    (prefixCoversCluster_of_prefix_cofinite σ endU endV B e
      (prefix_cofinite_of_last hn σ he))

end ReachDomination
end OSSS
end StatMech

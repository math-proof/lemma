import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.ReachDomination.Part3
open MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.ReachDomination


/--
[reachOpen_stable_to_B](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachDomination.lean)
-/
@[path]
private lemma reachOpen_stable_to_B_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {X w : ConfigSpace E}
  {B : Set V}
  {x b : V}
-- given
  (hagree : ∀ e', IncidentCluster endU endV X B e' → w e' = X e')
  (hb : b ∈ B)
  (h : ReachOpen endU endV X x b) :
-- imply
  ReachOpen endU endV w x b := by
-- proof
  apply StatMech.OSSS.ReachDomination.reachOpen_stable_to_B hagree hb h

/--
[connOpenSet_stable_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachDomination.lean)
-/
@[path]
private lemma connOpenSet_stable_of_agree_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {X w : ConfigSpace E}
  {B : Set V}
  {x : V}
-- given
  (hagree : ∀ e', IncidentCluster endU endV X B e' → w e' = X e')
  (h : ConnOpenSet endU endV X x B) :
-- imply
  ConnOpenSet endU endV w x B := by
-- proof
  apply StatMech.OSSS.ReachDomination.connOpenSet_stable_of_agree hagree h

/--
[reachOpen_stable_from_B](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachDomination.lean)
-/
@[path]
private lemma reachOpen_stable_from_B_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {X w : ConfigSpace E}
  {B : Set V}
  {b y : V}
-- given
  (hagree : ∀ e', IncidentCluster endU endV X B e' → w e' = X e')
  (hb : ConnOpenSet endU endV X b B)
  (h : ReachOpen endU endV w b y) :
-- imply
  ConnOpenSet endU endV X y B := by
-- proof
  apply StatMech.OSSS.ReachDomination.reachOpen_stable_from_B hagree hb h

/--
[connOpenSet_iff_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachDomination.lean)
-/
@[path]
private lemma connOpenSet_iff_of_agree_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {X w : ConfigSpace E}
  {B : Set V}
  {x : V}
-- given
  (hagree : ∀ e', IncidentCluster endU endV X B e' → w e' = X e') :
-- imply
  ConnOpenSet endU endV w x B ↔ ConnOpenSet endU endV X x B := by
-- proof
  apply StatMech.OSSS.ReachDomination.connOpenSet_iff_of_agree hagree

/--
[clusterMeasurable_indicatorConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachDomination.lean)
-/
@[path]
private lemma clusterMeasurable_indicatorConn_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {B C : Set V} :
-- imply
  ClusterMeasurable (indicatorConn endU endV B C) endU endV B := by
-- proof
  apply StatMech.OSSS.ReachDomination.clusterMeasurable_indicatorConn endU endV B C

/--
[detAtC_of_not_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachDomination.lean)
-/
@[path]
private lemma detAtC_of_not_incident_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {endU endV : E → V}
  {B : Set V}
  {e : E}
  {X : ConfigSpace E}
-- given
  (hfmeas : ClusterMeasurable f endU endV B)
  (hcover : PrefixCoversCluster σ endU endV B e)
  (hnotincid : ¬ IncidentCluster endU endV X B e) :
-- imply
  detAtC (σ : Fin n → E) f X (σ.symm e : ℕ) := by
-- proof
  apply StatMech.OSSS.ReachDomination.detAtC_of_not_incident σ endU endV B e X hfmeas hcover hnotincid

/--
[frontierConn_of_clusterMeasurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachDomination.lean)
-/
@[path]
private lemma frontierConn_of_clusterMeasurable_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {endU endV : E → V}
  {B : Set V}
  {e : E}
-- given
  (hfmeas : ClusterMeasurable f endU endV B)
  (hcover : PrefixCoversCluster σ endU endV B e) :
-- imply
  FrontierConn σ f endU endV B e := by
-- proof
  apply StatMech.OSSS.ReachDomination.frontierConn_of_clusterMeasurable σ endU endV B e hfmeas hcover

/--
[reachProb_le_connBox_of_clusterMeasurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachDomination.lean)
-/
@[path]
private lemma reachProb_le_connBox_of_clusterMeasurable_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {k : ℕ}
  {e : E}
  [DecidablePred (fun X => ConnOpenSet endU endV X (endU e) (vertexBoundary d k))]
  [DecidablePred (fun X => ConnOpenSet endU endV X (endV e) (vertexBoundary d k))]
  [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k))]
  [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k))]
-- given
  (hμ0 : ∀ ω, 0 ≤ μ ω)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hfmeas : ClusterMeasurable f endU endV (vertexBoundary d k))
  (hcover : PrefixCoversCluster σ endU endV (vertexBoundary d k) e) :
-- imply
  reachProb μ σ f e ≤ Lindeberg.mean μ (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0) + Lindeberg.mean μ (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.ReachDomination.reachProb_le_connBox_of_clusterMeasurable hμ0 σ hinj hcoh hadj k e hfmeas hcover

/--
[os_cov_lower_bound_from_clusterMeasurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachDomination.lean)
-/
@[path]
private lemma os_cov_lower_bound_from_clusterMeasurable_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {k : ℕ}
  {D : ℝ}
  [∀ e X, Decidable (ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k))]
  [∀ e X, Decidable (ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k))]
  [∀ e X, Decidable (ConnOpenSet endU endV X (endU e) (vertexBoundary d k))]
  [∀ e X, Decidable (ConnOpenSet endU endV X (endV e) (vertexBoundary d k))]
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1)
  (hidem : ∀ ω, f ω * f ω = f ω)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hDpos : 0 < D)
  (hfmeas : ClusterMeasurable f endU endV (vertexBoundary d k))
  (hcover : ∀ e, PrefixCoversCluster σ endU endV (vertexBoundary d k) e)
  (hbox : ∀ e, Lindeberg.mean μ (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0) + Lindeberg.mean μ (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0) ≤ D) :
-- imply
  Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) / D ≤ ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.ReachDomination.os_cov_lower_bound_from_clusterMeasurable hpos hμ1 hFKG hmono σ hf hf0 hf1 hidem hinj hcoh hadj k D hDpos hfmeas hcover hbox

/--
[prefixCoversCluster_of_prefix_cofinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachDomination.lean)
-/
@[path]
private lemma prefixCoversCluster_of_prefix_cofinite_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {n : ℕ}
  {σ : Fin n ≃ E}
  {endU endV : E → V}
  {B : Set V}
  {e : E}
-- given
  (hcofin : ∀ e' : E, e' ≠ e → e' ∈ prefixSet (σ : Fin n → E) (σ.symm e : ℕ)) :
-- imply
  PrefixCoversCluster σ endU endV B e := by
-- proof
  apply StatMech.OSSS.ReachDomination.prefixCoversCluster_of_prefix_cofinite σ endU endV B e hcofin

/--
[prefix_cofinite_of_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachDomination.lean)
-/
@[path]
private lemma prefix_cofinite_of_last_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {n : ℕ}
  {σ : Fin n ≃ E}
  {e : E}
-- given
  (hn : 1 ≤ n)
  (he : (σ.symm e : ℕ) = n - 1) :
-- imply
  ∀ e' : E, e' ≠ e → e' ∈ prefixSet (σ : Fin n → E) (σ.symm e : ℕ) := by
-- proof
  apply StatMech.OSSS.ReachDomination.prefix_cofinite_of_last hn σ he

/--
[frontierConn_indicatorConn_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachDomination.lean)
-/
@[path]
private lemma frontierConn_indicatorConn_last_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {n : ℕ}
  {σ : Fin n ≃ E}
  {endU endV : E → V}
  {B C : Set V}
  {e : E}
-- given
  (hn : 1 ≤ n)
  (he : (σ.symm e : ℕ) = n - 1) :
-- imply
  FrontierConn σ (indicatorConn endU endV B C) endU endV B e := by
-- proof
  apply StatMech.OSSS.ReachDomination.frontierConn_indicatorConn_last hn σ endU endV B C he


-- created on 2026-10-23

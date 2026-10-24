import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.PrefixCoversClose
open MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.PrefixCoversClose


/--
[reachOpen_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PrefixCoversClose.lean)
-/
@[path]
private lemma reachOpen_mono_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {X w : ConfigSpace E}
  {x y : V}
-- given
  (hle : ∀ e, X e = true → w e = true)
  (h : ReachOpen endU endV X x y) :
-- imply
  ReachOpen endU endV w x y := by
-- proof
  apply StatMech.OSSS.PrefixCoversClose.reachOpen_mono hle h

/--
[connOpenSet_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PrefixCoversClose.lean)
-/
@[path]
private lemma connOpenSet_mono_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {X w : ConfigSpace E}
  {B : Set V}
  {x : V}
-- given
  (hle : ∀ e, X e = true → w e = true)
  (h : ConnOpenSet endU endV X x B) :
-- imply
  ConnOpenSet endU endV w x B := by
-- proof
  apply StatMech.OSSS.PrefixCoversClose.connOpenSet_mono hle h

/--
[incidentCluster_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PrefixCoversClose.lean)
-/
@[path]
private lemma incidentCluster_mono_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {X w : ConfigSpace E}
  {B : Set V}
  {e' : E}
-- given
  (hle : ∀ e, X e = true → w e = true)
  (h : IncidentCluster endU endV X B e') :
-- imply
  IncidentCluster endU endV w B e' := by
-- proof
  apply StatMech.OSSS.PrefixCoversClose.incidentCluster_mono hle h

/--
[le_topCfg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PrefixCoversClose.lean)
-/
@[path]
private lemma le_topCfg_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {X : ConfigSpace E}
  {B : Set V}
  {e' : E}
-- given
  (h : IncidentCluster endU endV X B e') :
-- imply
  IncidentCluster endU endV (topCfg E) B e' := by
-- proof
  apply StatMech.OSSS.PrefixCoversClose.le_topCfg h

/--
[prefixCoversCluster_iff_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PrefixCoversClose.lean)
-/
@[path]
private lemma prefixCoversCluster_iff_top_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {n : ℕ}
  {σ : Fin n ≃ E}
  {endU endV : E → V}
  {B : Set V}
  {e : E} :
-- imply
  PrefixCoversCluster σ endU endV B e ↔ ∀ e' : E, e' ≠ e → TopIncident endU endV B e' → e' ∈ prefixSet (σ : Fin n → E) (σ.symm e : ℕ) := by
-- proof
  apply StatMech.OSSS.PrefixCoversClose.prefixCoversCluster_iff_top σ endU endV B e

/--
[prefixCoversCluster_of_topIncident_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PrefixCoversClose.lean)
-/
@[path]
private lemma prefixCoversCluster_of_topIncident_subset_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {n : ℕ}
  {σ : Fin n ≃ E}
  {endU endV : E → V}
  {B : Set V}
  {e : E}
-- given
  (hsub : ∀ e' : E, e' ≠ e → TopIncident endU endV B e' → e' ∈ prefixSet (σ : Fin n → E) (σ.symm e : ℕ)) :
-- imply
  PrefixCoversCluster σ endU endV B e := by
-- proof
  apply StatMech.OSSS.PrefixCoversClose.prefixCoversCluster_of_topIncident_subset σ endU endV B e hsub

/--
[prefixCoversCluster_of_pos_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PrefixCoversClose.lean)
-/
@[path]
private lemma prefixCoversCluster_of_pos_lt_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {n : ℕ}
  {σ : Fin n ≃ E}
  {endU endV : E → V}
  {B : Set V}
  {e : E}
-- given
  (hpos : ∀ e' : E, e' ≠ e → TopIncident endU endV B e' → (σ.symm e' : ℕ) < (σ.symm e : ℕ)) :
-- imply
  PrefixCoversCluster σ endU endV B e := by
-- proof
  apply StatMech.OSSS.PrefixCoversClose.prefixCoversCluster_of_pos_lt σ endU endV B e hpos

/--
[clusterOrder_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PrefixCoversClose.lean)
-/
@[path]
private lemma clusterOrder_exists_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  [DecidablePred p]
  {n : ℕ}
-- given
  (p : E → Prop)
  (hn : Fintype.card E = n) :
-- imply
  ∃ σ : Fin n ≃ E, ∀ e' : E, (p e' ↔ (σ.symm e' : ℕ) < (Finset.univ.filter p).card) := by
-- proof
  apply StatMech.OSSS.PrefixCoversClose.clusterOrder_exists p n hn

/--
[prefixCoversCluster_clusterOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PrefixCoversClose.lean)
-/
@[path]
private lemma prefixCoversCluster_clusterOrder_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {n : ℕ}
  {σ : Fin n ≃ E}
  {endU endV : E → V}
  {B : Set V}
  {e : E}
-- given
  (hσ : ∀ e' : E, (TopIncident endU endV B e' ↔ (σ.symm e' : ℕ) < (Finset.univ.filter (TopIncident endU endV B)).card))
  (he : (Finset.univ.filter (TopIncident endU endV B)).card - 1 ≤ (σ.symm e : ℕ)) :
-- imply
  PrefixCoversCluster σ endU endV B e := by
-- proof
  apply StatMech.OSSS.PrefixCoversClose.prefixCoversCluster_clusterOrder σ endU endV B hσ e he

/--
[prefixCoversCluster_frontier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PrefixCoversClose.lean)
-/
@[path]
private lemma prefixCoversCluster_frontier_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {B : Set V}
  {n : ℕ}
-- given
  (hn : Fintype.card E = n)
  (hne : (Finset.univ.filter (TopIncident endU endV B)).Nonempty) :
-- imply
  ∃ (σ : Fin n ≃ E) (e : E), TopIncident endU endV B e ∧ PrefixCoversCluster σ endU endV B e := by
-- proof
  apply StatMech.OSSS.PrefixCoversClose.prefixCoversCluster_frontier endU endV B n hn hne

/--
[frontierConn_clusterOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PrefixCoversClose.lean)
-/
@[path]
private lemma frontierConn_clusterOrder_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {B C : Set V}
  {n : ℕ}
-- given
  (hn : Fintype.card E = n)
  (hne : (Finset.univ.filter (TopIncident endU endV B)).Nonempty) :
-- imply
  ∃ (σ : Fin n ≃ E) (e : E), TopIncident endU endV B e ∧ FrontierConn σ (indicatorConn endU endV B C) endU endV B e := by
-- proof
  apply StatMech.OSSS.PrefixCoversClose.frontierConn_clusterOrder endU endV B C n hn hne

/--
[not_forall_prefixCoversCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PrefixCoversClose.lean)
-/
@[path]
private lemma not_forall_prefixCoversCluster_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {n : ℕ}
  {σ : Fin n ≃ E}
  {endU endV : E → V}
  {B : Set V}
-- given
  (h2 : 2 ≤ (Finset.univ.filter (TopIncident endU endV B)).card) :
-- imply
  ¬ (∀ e : E, PrefixCoversCluster σ endU endV B e) := by
-- proof
  apply StatMech.OSSS.PrefixCoversClose.not_forall_prefixCoversCluster σ endU endV B h2

/--
[incidentCluster_of_queried_crossTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PrefixCoversClose.lean)
-/
@[path]
private lemma incidentCluster_of_queried_crossTree_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {B C : Set V}
  {l : List E}
  {disc₀ : Finset V}
  {ω : ConfigSpace E}
  {i : E}
-- given
  (hdisc₀ : ∀ x ∈ disc₀, x ∈ B)
  (hi : i ∈ (crossTree endU endV o C l disc₀).queried ω) :
-- imply
  IncidentCluster endU endV ω B i := by
-- proof
  apply StatMech.OSSS.PrefixCoversClose.incidentCluster_of_queried_crossTree endU endV o B C l disc₀ hdisc₀ ω i hi


-- created on 2026-10-23

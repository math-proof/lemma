import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianSetClusterReplacement
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[mem_finiteTreeCurrentCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianSetClusterReplacement.lean)
-/
@[path]
private lemma mem_finiteTreeCurrentCluster_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {A : Finset V}
  {v : V} :
-- imply
  v ∈ finiteTreeCurrentCluster G n A ↔ exists a, a ∈ A ∧ CurrentConnected G n a v := by
-- proof
  apply StatMech.FrontierA.mem_finiteTreeCurrentCluster G n A v

/--
[subset_finiteTreeCurrentCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianSetClusterReplacement.lean)
-/
@[path]
private lemma subset_finiteTreeCurrentCluster_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {A : Finset V} :
-- imply
  A ⊆ finiteTreeCurrentCluster G n A := by
-- proof
  apply StatMech.FrontierA.subset_finiteTreeCurrentCluster G n A

/--
[finiteTreeCurrentCluster_singleton_eq_compl_notConnComp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianSetClusterReplacement.lean)
-/
@[path]
private lemma finiteTreeCurrentCluster_singleton_eq_compl_notConnComp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {i : V} :
-- imply
  finiteTreeCurrentCluster G n {i} = (notConnComp G n i)ᶜ := by
-- proof
  apply StatMech.FrontierA.finiteTreeCurrentCluster_singleton_eq_compl_notConnComp G n i

/--
[finiteTree_clusters_intersect_iff_mem_generated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianSetClusterReplacement.lean)
-/
@[path]
private lemma finiteTree_clusters_intersect_iff_mem_generated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m n : Current V}
  {i k : V} :
-- imply
  (exists y, CurrentConnected G m i y ∧ CurrentConnected G n k y) ↔ k ∈ finiteTreeCurrentCluster G n (finiteTreeCurrentCluster G m {i}) := by
-- proof
  apply StatMech.FrontierA.finiteTree_clusters_intersect_iff_mem_generated G m n i k

/--
[finiteTreeCurrentCluster_noCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianSetClusterReplacement.lean)
-/
@[path]
private lemma finiteTreeCurrentCluster_noCrossing_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {A T : Finset V}
-- given
  (hcluster : finiteTreeCurrentCluster G n A = T) :
-- imply
  NoCrossing G n T := by
-- proof
  apply StatMech.FrontierA.finiteTreeCurrentCluster_noCrossing G n A T hcluster

/--
[finiteTreeCurrentCluster_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianSetClusterReplacement.lean)
-/
@[path]
private lemma finiteTreeCurrentCluster_congr_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n n' : Current V}
  {A T : Finset V}
-- given
  (hAT : A ⊆ T)
  (hcluster : finiteTreeCurrentCluster G n A = T)
  (hagree : ∀ e ∈ G.edgeFinset, ¬ edgeInside Tᶜ e -> n e = n' e) :
-- imply
  finiteTreeCurrentCluster G n' A = T := by
-- proof
  apply StatMech.FrontierA.finiteTreeCurrentCluster_congr G n n' A T hAT hcluster hagree

/--
[finiteTree_setCluster_sourceReplacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianSetClusterReplacement.lean)
-/
@[path]
private lemma finiteTree_setCluster_sourceReplacement_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A T : Finset V}
  {k l : V}
-- given
  (J : Sym2 V -> Real)
  (hAT : A ⊆ T)
  (hk : k ∉ T)
  (hl : l ∉ T) :
-- imply
  gatedSourcePairSum G beta J {k, l} ∅ (fun n => finiteTreeCurrentCluster G n A = T) = expectationJ G beta (couplingIn J Tᶜ) {k, l} * gatedSourcePairSum G beta J ∅ ∅ (fun n => finiteTreeCurrentCluster G n A = T) := by
-- proof
  apply StatMech.FrontierA.finiteTree_setCluster_sourceReplacement G beta J A T hAT hk hl


-- created on 2026-10-23

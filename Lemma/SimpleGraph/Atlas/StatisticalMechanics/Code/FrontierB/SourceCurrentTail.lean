import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.SourceCurrentTail
open MeasureTheory StatMech StatMech.FrontierB


/--
[currentWeight_le_currentSum_of_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SourceCurrentTail.lean)
-/
@[path]
private lemma currentWeight_le_currentSum_of_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hm : sources G (ofEdgeFun G m) = A) :
-- imply
  weight G beta J (ofEdgeFun G m) ≤ currentSum G beta J A := by
-- proof
  apply StatMech.FrontierB.currentWeight_le_currentSum_of_sources G beta J hbeta hJ A m hm

/--
[currentSum_empty_le_unrestricted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SourceCurrentTail.lean)
-/
@[path]
private lemma currentSum_empty_le_unrestricted_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  currentSum G beta J ∅ ≤ Real.exp (∑ e ∈ G.edgeFinset, beta * J e) := by
-- proof
  apply StatMech.FrontierB.currentSum_empty_le_unrestricted G beta J hbeta hJ

/--
[currentWitness_correlation_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SourceCurrentTail.lean)
-/
@[path]
private lemma currentWitness_correlation_lower_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hm : sources G (ofEdgeFun G m) = A) :
-- imply
  weight G beta J (ofEdgeFun G m) / Real.exp (∑ e ∈ G.edgeFinset, beta * J e) ≤ expectationJ G beta J A := by
-- proof
  apply StatMech.FrontierB.currentWitness_correlation_lower_bound G beta J hbeta hJ A m hm

/--
[localCurrentWitness_correlation_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SourceCurrentTail.lean)
-/
@[path]
private lemma localCurrentWitness_correlation_lower_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {S A : Finset V}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hm : sources G (ofEdgeFun G m) = A) :
-- imply
  weight G beta (couplingIn J S) (ofEdgeFun G m) / Real.exp (∑ e ∈ G.edgeFinset, beta * couplingIn J S e) ≤ expectationJ G beta J A := by
-- proof
  apply StatMech.FrontierB.localCurrentWitness_correlation_lower_bound G beta J hbeta hJ S A m hm

/--
[currentWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SourceCurrentTail.lean)
-/
@[path]
private lemma currentWeight_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e ∈ G.edgeFinset, 0 < J e) :
-- imply
  0 < weight G beta J (ofEdgeFun G m) := by
-- proof
  apply StatMech.FrontierB.currentWeight_pos G beta J hbeta hJ m

/--
[currentWeight_pos_of_positive_on_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SourceCurrentTail.lean)
-/
@[path]
private lemma currentWeight_pos_of_positive_on_support_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e : G.edgeFinset, m e ≠ 0 → 0 < J e.1) :
-- imply
  0 < weight G beta J (ofEdgeFun G m) := by
-- proof
  apply StatMech.FrontierB.currentWeight_pos_of_positive_on_support G beta J hbeta m hJ

/--
[walkEdges_subset_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SourceCurrentTail.lean)
-/
@[path]
private lemma walkEdges_subset_edgeFinset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {u v : V}
  {p : G.Walk u v} :
-- imply
  p.edges.toFinset ⊆ G.edgeFinset := by
-- proof
  apply StatMech.FrontierB.walkEdges_subset_edgeFinset G p

/--
[ofEdgeFun_pathEdgeCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SourceCurrentTail.lean)
-/
@[path]
private lemma ofEdgeFun_pathEdgeCurrent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {u v : V}
  {p : G.Walk u v} :
-- imply
  ofEdgeFun G (pathEdgeCurrent G p) = edgeIndicatorCurrent p.edges.toFinset := by
-- proof
  apply StatMech.FrontierB.ofEdgeFun_pathEdgeCurrent G p

/--
[sources_pathEdgeCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SourceCurrentTail.lean)
-/
@[path]
private lemma sources_pathEdgeCurrent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {u v : V}
  {p : G.Walk u v}
-- given
  (hp : p.IsPath)
  (huv : u ≠ v) :
-- imply
  sources G (ofEdgeFun G (pathEdgeCurrent G p)) = {u, v} := by
-- proof
  apply StatMech.FrontierB.sources_pathEdgeCurrent G p hp huv

/--
[pathCorrelationConstant_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SourceCurrentTail.lean)
-/
@[path]
private lemma pathCorrelationConstant_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {u v : V}
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {p : G.Walk u v}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e ∈ G.edgeFinset, 0 < J e)
  (hS : ∀ x ∈ p.support, x ∈ S) :
-- imply
  0 < pathCorrelationConstant G beta J S p := by
-- proof
  apply StatMech.FrontierB.pathCorrelationConstant_pos G beta J S p hbeta hJ hS

/--
[pathCorrelationConstant_le_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SourceCurrentTail.lean)
-/
@[path]
private lemma pathCorrelationConstant_le_expectation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {u v : V}
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {p : G.Walk u v}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hp : p.IsPath)
  (huv : u ≠ v) :
-- imply
  pathCorrelationConstant G beta J S p ≤ expectationJ G beta J {u, v} := by
-- proof
  apply StatMech.FrontierB.pathCorrelationConstant_le_expectation G beta J hbeta hJ S p hp huv

/--
[currentSum_pair_pos_of_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SourceCurrentTail.lean)
-/
@[path]
private lemma currentSum_pair_pos_of_path_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {u v : V}
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {p : G.Walk u v}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 < J e)
  (hp : p.IsPath)
  (huv : u ≠ v) :
-- imply
  0 < currentSum G beta J {u, v} := by
-- proof
  apply StatMech.FrontierB.currentSum_pair_pos_of_path G beta J hbeta hJ p hp huv

/--
[source_current_tail_doubling_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SourceCurrentTail.lean)
-/
@[path]
private lemma source_current_tail_doubling_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {e : G.edgeFinset}
  {K : ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ f, 0 ≤ J f) :
-- imply
  (∑' m : EdgeCurrent G, if sources G (ofEdgeFun G m) = A ∧ K ≤ m e then weight G beta J (ofEdgeFun G m) else 0) ≤ ((2 : ℝ) ^ K)⁻¹ * currentSum G beta (doubledEdgeCoupling J e.1) A := by
-- proof
  apply StatMech.FrontierB.source_current_tail_doubling_le G beta J hbeta hJ A e K

/--
[currentSum_doubledEdgeCoupling_source_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SourceCurrentTail.lean)
-/
@[path]
private lemma currentSum_doubledEdgeCoupling_source_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {e : G.edgeFinset}
  {c : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ f, 0 ≤ J f)
  (hc : 0 < c)
  (hcorr : c ≤ expectationJ G beta J A) :
-- imply
  currentSum G beta (doubledEdgeCoupling J e.1) A ≤ (Real.exp (beta * J e.1) / c) * currentSum G beta J A := by
-- proof
  apply StatMech.FrontierB.currentSum_doubledEdgeCoupling_source_le G beta J hbeta hJ A e c hc hcorr

/--
[sourceCurrentMeasure_edge_exponential_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SourceCurrentTail.lean)
-/
@[path]
private lemma sourceCurrentMeasure_edge_exponential_tail_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {e : G.edgeFinset}
  {c : ℝ}
  {K : ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ f, 0 ≤ J f)
  (hA : 0 < currentSum G beta J A)
  (hc : 0 < c)
  (hcorr : c ≤ expectationJ G beta J A) :
-- imply
  (sourceCurrentMeasure G beta J hbeta hJ A hA : Measure (EdgeCurrent G)) {m | K ≤ m e} ≤ ENNReal.ofReal (Real.exp (beta * J e.1) / (c * (2 : ℝ) ^ K)) := by
-- proof
  apply StatMech.FrontierB.sourceCurrentMeasure_edge_exponential_tail_le G beta J hbeta hJ A hA e c hc hcorr K

/--
[sourceCurrentMeasure_edge_inverse_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SourceCurrentTail.lean)
-/
@[path]
private lemma sourceCurrentMeasure_edge_inverse_tail_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {e : G.edgeFinset}
  {c : ℝ}
  {K : ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ f, 0 ≤ J f)
  (hA : 0 < currentSum G beta J A)
  (hc : 0 < c)
  (hcorr : c ≤ expectationJ G beta J A)
  (hK : 0 < K) :
-- imply
  (sourceCurrentMeasure G beta J hbeta hJ A hA : Measure (EdgeCurrent G)) {m | K ≤ m e} ≤ ENNReal.ofReal (Real.exp (beta * J e.1) / (c * K)) := by
-- proof
  apply StatMech.FrontierB.sourceCurrentMeasure_edge_inverse_tail_le G beta J hbeta hJ A hA e c hc hcorr K hK


-- created on 2026-10-23

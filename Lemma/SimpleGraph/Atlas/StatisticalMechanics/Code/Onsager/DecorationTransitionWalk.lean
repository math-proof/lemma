import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWalk.Part4
open StatMech StatMech.Onsager


/--
[ons_decGraph_adj_of_portLineAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decGraph_adj_of_portLineAdj_eq
  {L : ℕ}
  {site : ZMod L × ZMod L}
  {a b : Fin 4}
-- given
  (h : ons_portLineAdj a b) :
-- imply
  (ons_decGraph L).Adj (site, a) (site, b) := by
-- proof
  apply StatMech.Onsager.ons_decGraph_adj_of_portLineAdj L site h

/--
[ons_decGraph_adj01](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decGraph_adj01_eq
  {L : ℕ}
  {site : ZMod L × ZMod L} :
-- imply
  (ons_decGraph L).Adj (site, 0) (site, 1) := by
-- proof
  apply StatMech.Onsager.ons_decGraph_adj01 L site

/--
[ons_decGraph_adj10](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decGraph_adj10_eq
  {L : ℕ}
  {site : ZMod L × ZMod L} :
-- imply
  (ons_decGraph L).Adj (site, 1) (site, 0) := by
-- proof
  apply StatMech.Onsager.ons_decGraph_adj10 L site

/--
[ons_decGraph_adj12](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decGraph_adj12_eq
  {L : ℕ}
  {site : ZMod L × ZMod L} :
-- imply
  (ons_decGraph L).Adj (site, 1) (site, 2) := by
-- proof
  apply StatMech.Onsager.ons_decGraph_adj12 L site

/--
[ons_decGraph_adj21](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decGraph_adj21_eq
  {L : ℕ}
  {site : ZMod L × ZMod L} :
-- imply
  (ons_decGraph L).Adj (site, 2) (site, 1) := by
-- proof
  apply StatMech.Onsager.ons_decGraph_adj21 L site

/--
[ons_decGraph_adj23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decGraph_adj23_eq
  {L : ℕ}
  {site : ZMod L × ZMod L} :
-- imply
  (ons_decGraph L).Adj (site, 2) (site, 3) := by
-- proof
  apply StatMech.Onsager.ons_decGraph_adj23 L site

/--
[ons_decGraph_adj32](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decGraph_adj32_eq
  {L : ℕ}
  {site : ZMod L × ZMod L} :
-- imply
  (ons_decGraph L).Adj (site, 3) (site, 2) := by
-- proof
  apply StatMech.Onsager.ons_decGraph_adj32 L site

/--
[ons_decChainPathIndices_00](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decChainPathIndices_00_eq :
-- imply
  ons_decChainPathIndices 0 0 = ∅ := by
-- proof
  apply StatMech.Onsager.ons_decChainPathIndices_00

/--
[ons_decChainPathIndices_01](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decChainPathIndices_01_eq :
-- imply
  ons_decChainPathIndices 0 1 = {0} := by
-- proof
  apply StatMech.Onsager.ons_decChainPathIndices_01

/--
[ons_decChainPathIndices_02](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decChainPathIndices_02_eq :
-- imply
  ons_decChainPathIndices 0 2 = {0, 1} := by
-- proof
  apply StatMech.Onsager.ons_decChainPathIndices_02

/--
[ons_decChainPathIndices_03](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decChainPathIndices_03_eq :
-- imply
  ons_decChainPathIndices 0 3 = Finset.univ := by
-- proof
  apply StatMech.Onsager.ons_decChainPathIndices_03

/--
[ons_decChainPathIndices_10](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decChainPathIndices_10_eq :
-- imply
  ons_decChainPathIndices 1 0 = {0} := by
-- proof
  apply StatMech.Onsager.ons_decChainPathIndices_10

/--
[ons_decChainPathIndices_11](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decChainPathIndices_11_eq :
-- imply
  ons_decChainPathIndices 1 1 = ∅ := by
-- proof
  apply StatMech.Onsager.ons_decChainPathIndices_11

/--
[ons_decChainPathIndices_12](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decChainPathIndices_12_eq :
-- imply
  ons_decChainPathIndices 1 2 = {1} := by
-- proof
  apply StatMech.Onsager.ons_decChainPathIndices_12

/--
[ons_decChainPathIndices_13](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decChainPathIndices_13_eq :
-- imply
  ons_decChainPathIndices 1 3 = {1, 2} := by
-- proof
  apply StatMech.Onsager.ons_decChainPathIndices_13

/--
[ons_decChainPathIndices_20](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decChainPathIndices_20_eq :
-- imply
  ons_decChainPathIndices 2 0 = {0, 1} := by
-- proof
  apply StatMech.Onsager.ons_decChainPathIndices_20

/--
[ons_decChainPathIndices_21](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decChainPathIndices_21_eq :
-- imply
  ons_decChainPathIndices 2 1 = {1} := by
-- proof
  apply StatMech.Onsager.ons_decChainPathIndices_21

/--
[ons_decChainPathIndices_22](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decChainPathIndices_22_eq :
-- imply
  ons_decChainPathIndices 2 2 = ∅ := by
-- proof
  apply StatMech.Onsager.ons_decChainPathIndices_22

/--
[ons_decChainPathIndices_23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decChainPathIndices_23_eq :
-- imply
  ons_decChainPathIndices 2 3 = {2} := by
-- proof
  apply StatMech.Onsager.ons_decChainPathIndices_23

/--
[ons_decChainPathIndices_30](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decChainPathIndices_30_eq :
-- imply
  ons_decChainPathIndices 3 0 = Finset.univ := by
-- proof
  apply StatMech.Onsager.ons_decChainPathIndices_30

/--
[ons_decChainPathIndices_31](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decChainPathIndices_31_eq :
-- imply
  ons_decChainPathIndices 3 1 = {1, 2} := by
-- proof
  apply StatMech.Onsager.ons_decChainPathIndices_31

/--
[ons_decChainPathIndices_32](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decChainPathIndices_32_eq :
-- imply
  ons_decChainPathIndices 3 2 = {2} := by
-- proof
  apply StatMech.Onsager.ons_decChainPathIndices_32

/--
[ons_decChainPathIndices_33](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decChainPathIndices_33_eq :
-- imply
  ons_decChainPathIndices 3 3 = ∅ := by
-- proof
  apply StatMech.Onsager.ons_decChainPathIndices_33

/--
[ons_exists_decPortChainWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_exists_decPortChainWalk_eq
  {L : ℕ}
  {site : ZMod L × ZMod L}
  {a b : Fin 4} :
-- imply
  ∃ p : (ons_decGraph L).Walk (site, a) (site, b), p.edges.toFinset = ons_decChainPathEdges site a b := by
-- proof
  apply StatMech.Onsager.ons_exists_decPortChainWalk L site a b

/--
[ons_decPortChainWalk_edges_toFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decPortChainWalk_edges_toFinset_eq
  {L : ℕ}
  {site : ZMod L × ZMod L}
  {a b : Fin 4} :
-- imply
  (ons_decPortChainWalk L site a b).edges.toFinset = ons_decChainPathEdges site a b := by
-- proof
  apply StatMech.Onsager.ons_decPortChainWalk_edges_toFinset L site a b

/--
[ons_exists_decPortChainPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_exists_decPortChainPath_eq
  {L : ℕ}
  {site : ZMod L × ZMod L}
  {a b : Fin 4} :
-- imply
  ∃ p : (ons_decGraph L).Walk (site, a) (site, b), p.IsPath ∧ p.edges.toFinset = ons_decChainPathEdges site a b := by
-- proof
  apply StatMech.Onsager.ons_exists_decPortChainPath L site a b

/--
[ons_decPortChainPath_isPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decPortChainPath_isPath_eq
  {L : ℕ}
  {site : ZMod L × ZMod L}
  {a b : Fin 4} :
-- imply
  (ons_decPortChainPath L site a b).IsPath := by
-- proof
  apply StatMech.Onsager.ons_decPortChainPath_isPath L site a b

/--
[ons_decPortChainPath_edges_toFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decPortChainPath_edges_toFinset_eq
  {L : ℕ}
  {site : ZMod L × ZMod L}
  {a b : Fin 4} :
-- imply
  (ons_decPortChainPath L site a b).edges.toFinset = ons_decChainPathEdges site a b := by
-- proof
  apply StatMech.Onsager.ons_decPortChainPath_edges_toFinset L site a b

/--
[ons_dartRev_fst_eq_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_dartRev_fst_eq_step_eq
  {L : ℕ}
  {d : ons_Dart L} :
-- imply
  (ons_dartRev L d).1 = ons_dirStep L d.2 d.1 := by
-- proof
  apply StatMech.Onsager.ons_dartRev_fst_eq_step L d

/--
[ons_decTransitionWalk_edges_toFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decTransitionWalk_edges_toFinset_eq
  {L : ℕ}
  {d₂ d₁ : ons_Dart L}
-- given
  (hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1) :
-- imply
  (ons_decTransitionWalk L d₂ d₁ hstep).edges.toFinset = insert s(d₁, ons_dartRev L d₁) (ons_decChainPathEdges d₂.1 (d₁.2 + 2) d₂.2) := by
-- proof
  apply StatMech.Onsager.ons_decTransitionWalk_edges_toFinset L d₂ d₁ hstep

/--
[ons_decChainEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decChainEdge_injective_eq
  {L : ℕ}
  {site : ZMod L × ZMod L} :
-- imply
  Function.Injective (ons_decChainEdge site) := by
-- proof
  apply StatMech.Onsager.ons_decChainEdge_injective site

/--
[ons_externalEdge_not_mem_chainPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_externalEdge_not_mem_chainPath_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {site : ZMod L × ZMod L}
  {a b : Fin 4} :
-- imply
  s(d, ons_dartRev L d) ∉ ons_decChainPathEdges site a b := by
-- proof
  apply StatMech.Onsager.ons_externalEdge_not_mem_chainPath L d site a b

/--
[ons_decTransitionWalk_isTrail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decTransitionWalk_isTrail_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d₂ d₁ : ons_Dart L}
-- given
  (hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1) :
-- imply
  (ons_decTransitionWalk L d₂ d₁ hstep).IsTrail := by
-- proof
  apply StatMech.Onsager.ons_decTransitionWalk_isTrail L d₂ d₁ hstep

/--
[ons_decTransitionExponent_eq_walkEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decTransitionExponent_eq_walkEdges_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d₂ d₁ : ons_Dart L}
-- given
  (hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1) :
-- imply
  ons_decTransitionExponent L d₂ d₁ = ons_finsetExponent (ons_decTransitionWalk L d₂ d₁ hstep).edges.toFinset := by
-- proof
  apply StatMech.Onsager.ons_decTransitionExponent_eq_walkEdges L d₂ d₁ hstep

/--
[ons_decTransitionExponent_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_decTransitionExponent_prod_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {d₂ d₁ : ons_Dart L}
-- given
  (hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1) :
-- imply
  (ons_decTransitionExponent L d₂ d₁).prod (fun edge n ↦ decWeight edge ^ n) = ons_decTransitionWeight L decWeight d₂ d₁ := by
-- proof
  apply StatMech.Onsager.ons_decTransitionExponent_prod L decWeight d₂ d₁ hstep

/--
[ons_KWmatDecorationWeightedPhase_entry_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_KWmatDecorationWeightedPhase_entry_factor_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {omega u v : ℂ}
  {d₂ d₁ : ons_Dart L} :
-- imply
  ons_KWmatDecorationWeightedPhase L decWeight omega u v d₂ d₁ = ons_decTransitionScalar L omega u v d₂ d₁ * (ons_decTransitionExponent L d₂ d₁).prod (fun edge n ↦ decWeight edge ^ n) := by
-- proof
  apply StatMech.Onsager.ons_KWmatDecorationWeightedPhase_entry_factor L decWeight omega u v d₂ d₁

/--
[ons_finsuppProd_sum_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_finsuppProd_sum_pow_eq
  [Fintype I]
  [DecidableEq E]
  [CommMonoid R]
  {m : I → E →₀ ℕ}
  {weight : E → R} :
-- imply
  (∑ i, m i).prod (fun edge n ↦ weight edge ^ n) = ∏ i, (m i).prod (fun edge n ↦ weight edge ^ n) := by
-- proof
  apply StatMech.Onsager.ons_finsuppProd_sum_pow m weight

/--
[ons_loopWeight_KWmatDecorationWeightedPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTransitionWalk.lean)
-/
@[path]
private lemma ons_loopWeight_KWmatDecorationWeightedPhase_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {decWeight : ons_DecEdge L → ℂ}
  {omega u v : ℂ}
  {d : Fin n → ons_Dart L} :
-- imply
  ons_loopWeight (ons_KWmatDecorationWeightedPhase L decWeight omega u v) d = ons_decLoopScalar L omega u v d * (ons_decLoopExponent L d).prod (fun edge k ↦ decWeight edge ^ k) := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_KWmatDecorationWeightedPhase decWeight omega u v d


-- created on 2026-10-23

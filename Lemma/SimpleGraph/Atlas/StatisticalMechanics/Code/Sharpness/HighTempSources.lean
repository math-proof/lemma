import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.HighTempSources
open Finset StatMech StatMech.Sharpness


/--
[hasOddBoundary_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSources.lean)
-/
@[path]
private lemma hasOddBoundary_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : Finset (Sym2 V)} :
-- imply
  HasOddBoundary F ∅ ↔ IsEvenSubgraph F := by
-- proof
  apply StatMech.Sharpness.hasOddBoundary_empty G F

/--
[sum_spinProd_prod_bond_subgraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSources.lean)
-/
@[path]
private lemma sum_spinProd_prod_bond_subgraph_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
  {F : Finset (Sym2 V)}
-- given
  (hF : ∀ e ∈ F, ¬ e.IsDiag) :
-- imply
  (∑ s : ConfigSpace V, spinProd A s * ∏ e ∈ F, bond s e) = if HasOddBoundary F A then (2 : ℝ) ^ Fintype.card V else 0 := by
-- proof
  apply StatMech.Sharpness.sum_spinProd_prod_bond_subgraph G A F hF

/--
[spinProd_weight_high_temp_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSources.lean)
-/
@[path]
private lemma spinProd_weight_high_temp_expansion_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {A : Finset V} :
-- imply
  (∑ s : ConfigSpace V, spinProd A s * isingWeight G beta 0 s) = (2 : ℝ) ^ Fintype.card V * (Real.cosh beta) ^ G.edgeFinset.card * ∑ F ∈ G.edgeFinset.powerset.filter (fun F => HasOddBoundary F A), (Real.tanh beta) ^ F.card := by
-- proof
  apply StatMech.Sharpness.spinProd_weight_high_temp_expansion G beta A

/--
[expectation_spinProd_high_temp_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSources.lean)
-/
@[path]
private lemma expectation_spinProd_high_temp_ratio_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {A : Finset V} :
-- imply
  isingExpectation G beta 0 (spinProd A) = (∑ F ∈ G.edgeFinset.powerset.filter (fun F => HasOddBoundary F A), (Real.tanh beta) ^ F.card) / (∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph, (Real.tanh beta) ^ F.card) := by
-- proof
  apply StatMech.Sharpness.expectation_spinProd_high_temp_ratio G beta A

/--
[boltzmannJ_high_temp_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSources.lean)
-/
@[path]
private lemma boltzmannJ_high_temp_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {s : ConfigSpace V} :
-- imply
  boltzmannJ G beta J s = (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) * ∏ e ∈ G.edgeFinset, (1 + Real.tanh (beta * J e) * bond s e) := by
-- proof
  apply StatMech.Sharpness.boltzmannJ_high_temp_factor G beta J s

/--
[spinProd_boltzmannJ_high_temp_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSources.lean)
-/
@[path]
private lemma spinProd_boltzmannJ_high_temp_expansion_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V} :
-- imply
  (∑ s : ConfigSpace V, spinProd A s * boltzmannJ G beta J s) = (2 : ℝ) ^ Fintype.card V * (∏ e ∈ G.edgeFinset, Real.cosh (beta * J e)) * ∑ F ∈ G.edgeFinset.powerset.filter (fun F => HasOddBoundary F A), highTempSubgraphWeight beta J F := by
-- proof
  apply StatMech.Sharpness.spinProd_boltzmannJ_high_temp_expansion G beta J A

/--
[expectationJ_high_temp_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSources.lean)
-/
@[path]
private lemma expectationJ_high_temp_ratio_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V} :
-- imply
  expectationJ G beta J A = (∑ F ∈ G.edgeFinset.powerset.filter (fun F => HasOddBoundary F A), highTempSubgraphWeight beta J F) / (∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph, highTempSubgraphWeight beta J F) := by
-- proof
  apply StatMech.Sharpness.expectationJ_high_temp_ratio G beta J A

/--
[incidentFlux_edgeIndicatorCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSources.lean)
-/
@[path]
private lemma incidentFlux_edgeIndicatorCurrent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : Finset (Sym2 V)}
  {v : V}
-- given
  (hF : F ⊆ G.edgeFinset) :
-- imply
  incidentFlux G (edgeIndicatorCurrent F) v = incCount F v := by
-- proof
  apply StatMech.Sharpness.incidentFlux_edgeIndicatorCurrent G F hF v

/--
[sources_edgeIndicatorCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSources.lean)
-/
@[path]
private lemma sources_edgeIndicatorCurrent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : Finset (Sym2 V)}
  {A : Finset V}
-- given
  (hF : F ⊆ G.edgeFinset)
  (hbd : HasOddBoundary F A) :
-- imply
  sources G (edgeIndicatorCurrent F) = A := by
-- proof
  apply StatMech.Sharpness.sources_edgeIndicatorCurrent G F A hF hbd

/--
[hasOddBoundary_backbone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSources.lean)
-/
@[path]
private lemma hasOddBoundary_backbone_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : Finset (Sym2 V)}
  {o z : V}
-- given
  (hF : F ⊆ G.edgeFinset)
  (hoz : o ≠ z)
  (hbd : HasOddBoundary F {o, z}) :
-- imply
  Nonempty (IsBackbonePath G (edgeIndicatorCurrent F) o z) := by
-- proof
  apply StatMech.Sharpness.hasOddBoundary_backbone G F hF hoz hbd

/--
[hasOddBoundary_firstExit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSources.lean)
-/
@[path]
private lemma hasOddBoundary_firstExit_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : Finset (Sym2 V)}
  {o z : V}
  {S : Finset V}
-- given
  (hF : F ⊆ G.edgeFinset)
  (hoz : o ≠ z)
  (hbd : HasOddBoundary F {o, z})
  (ho : o ∈ S)
  (hz : z ∉ S) :
-- imply
  ∃ x ∈ S, ∃ y ∉ S, s(x, y) ∈ F := by
-- proof
  apply StatMech.Sharpness.hasOddBoundary_firstExit G F hF hoz hbd S ho hz


-- created on 2026-10-23

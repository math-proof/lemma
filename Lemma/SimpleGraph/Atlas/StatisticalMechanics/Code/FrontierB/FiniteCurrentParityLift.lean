import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentParityLift.Part2
open MeasureTheory StatMech StatMech.FrontierB


/--
[mem_currentParitySupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParityLift.lean)
-/
@[path]
private lemma mem_currentParitySupport_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : EdgeCurrent G}
  {e : G.edgeFinset} :
-- imply
  e.1 ∈ currentParitySupport G m ↔ Odd (m e) := by
-- proof
  apply StatMech.FrontierB.mem_currentParitySupport G m e

/--
[currentParitySupport_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParityLift.lean)
-/
@[path]
private lemma currentParitySupport_subset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : EdgeCurrent G} :
-- imply
  currentParitySupport G m ⊆ G.edgeFinset := by
-- proof
  apply StatMech.FrontierB.currentParitySupport_subset G m

/--
[currentParitySupport_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParityLift.lean)
-/
@[path]
private lemma currentParitySupport_eq_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : Finset (Sym2 V)}
  {m : EdgeCurrent G}
-- given
  (hH : H ⊆ G.edgeFinset) :
-- imply
  currentParitySupport G m = H ↔ ∀ e : G.edgeFinset, if e.1 ∈ H then Odd (m e) else Even (m e) := by
-- proof
  apply StatMech.FrontierB.currentParitySupport_eq_iff G H hH m

/--
[sources_eq_sources_currentParitySupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParityLift.lean)
-/
@[path]
private lemma sources_eq_sources_currentParitySupport_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : EdgeCurrent G} :
-- imply
  sources G (ofEdgeFun G m) = sources G (edgeIndicatorCurrent (currentParitySupport G m)) := by
-- proof
  apply StatMech.FrontierB.sources_eq_sources_currentParitySupport G m

/--
[sources_empty_iff_currentParitySupport_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParityLift.lean)
-/
@[path]
private lemma sources_empty_iff_currentParitySupport_even_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : EdgeCurrent G} :
-- imply
  sources G (ofEdgeFun G m) = ∅ ↔ IsEvenSubgraph (currentParitySupport G m) := by
-- proof
  apply StatMech.FrontierB.sources_empty_iff_currentParitySupport_even G m

/--
[summable_parityCurrentTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParityLift.lean)
-/
@[path]
private lemma summable_parityCurrentTerm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ} :
-- imply
  Summable (parityCurrentTerm beta) := by
-- proof
  apply StatMech.FrontierB.summable_parityCurrentTerm G beta

/--
[summable_parityCurrentTerm_filter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParityLift.lean)
-/
@[path]
private lemma summable_parityCurrentTerm_filter_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  [DecidablePred Q]
-- given
  (Q : ℕ → Prop) :
-- imply
  Summable (fun k => if Q k then parityCurrentTerm beta k else 0) := by
-- proof
  apply StatMech.FrontierB.summable_parityCurrentTerm_filter G beta Q

/--
[tsum_parityCurrentTerm_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParityLift.lean)
-/
@[path]
private lemma tsum_parityCurrentTerm_even_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ} :
-- imply
  (∑' k : ℕ, if Even k then parityCurrentTerm beta k else 0) = Real.cosh beta := by
-- proof
  apply StatMech.FrontierB.tsum_parityCurrentTerm_even G beta

/--
[tsum_parityCurrentTerm_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParityLift.lean)
-/
@[path]
private lemma tsum_parityCurrentTerm_odd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ} :
-- imply
  (∑' k : ℕ, if Odd k then parityCurrentTerm beta k else 0) = Real.sinh beta := by
-- proof
  apply StatMech.FrontierB.tsum_parityCurrentTerm_odd G beta

/--
[fixedParity_weight_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParityLift.lean)
-/
@[path]
private lemma fixedParity_weight_tsum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {H : Finset (Sym2 V)}
-- given
  (hbeta : 0 ≤ beta)
  (hH : H ⊆ G.edgeFinset) :
-- imply
  (∑' m : EdgeCurrent G, if currentParitySupport G m = H then weight G beta (fun _ => 1) (ofEdgeFun G m) else 0) = ∏ e ∈ G.edgeFinset, if e ∈ H then Real.sinh beta else Real.cosh beta := by
-- proof
  apply StatMech.FrontierB.fixedParity_weight_tsum G beta hbeta H hH

/--
[fixedParity_weight_tsum_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParityLift.lean)
-/
@[path]
private lemma fixedParity_weight_tsum_closed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {H : Finset (Sym2 V)}
-- given
  (hbeta : 0 ≤ beta)
  (hH : H ⊆ G.edgeFinset) :
-- imply
  (∑' m : EdgeCurrent G, if currentParitySupport G m = H then weight G beta (fun _ => 1) (ofEdgeFun G m) else 0) = Real.cosh beta ^ G.edgeFinset.card * Real.tanh beta ^ H.card := by
-- proof
  apply StatMech.FrontierB.fixedParity_weight_tsum_closed G beta hbeta H hH

/--
[currentSum_unit_eq_parityPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParityLift.lean)
-/
@[path]
private lemma currentSum_unit_eq_parityPartition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ} :
-- imply
  currentSum G beta (fun _ => 1) ∅ = Real.cosh beta ^ G.edgeFinset.card * freeParityPartition G beta := by
-- proof
  apply StatMech.FrontierB.currentSum_unit_eq_parityPartition G beta

/--
[tsum_currentRawMass_fixedParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParityLift.lean)
-/
@[path]
private lemma tsum_currentRawMass_fixedParity_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {H : Finset (Sym2 V)}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  (∑' m : EdgeCurrent G, if currentParitySupport G m = H then currentRawMass G beta (fun _ => 1) ∅ m else 0) = freeParityRawMass G beta H * ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) := by
-- proof
  apply StatMech.FrontierB.tsum_currentRawMass_fixedParity G beta hbeta H

/--
[sourcelessCurrentPMF_map_currentParitySupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParityLift.lean)
-/
@[path]
private lemma sourcelessCurrentPMF_map_currentParitySupport_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  PMF.map (currentParitySupport G) (sourcelessCurrentPMF G beta (fun _ => 1) hbeta (fun _ => zero_le_one)) = freeParityPMF G beta hbeta := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentPMF_map_currentParitySupport G beta hbeta

/--
[sourcelessCurrentMeasure_map_currentParitySupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParityLift.lean)
-/
@[path]
private lemma sourcelessCurrentMeasure_map_currentParitySupport_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  Measure.map (currentParitySupport G) (sourcelessCurrentMeasure G beta (fun _ => 1) hbeta (fun _ => zero_le_one) : Measure (EdgeCurrent G)) = (freeParityMeasure G beta hbeta : Measure (Finset (Sym2 V))) := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentMeasure_map_currentParitySupport G beta hbeta

/--
[sourcelessCurrentMeasure_parityAvoid_eq_spinExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParityLift.lean)
-/
@[path]
private lemma sourcelessCurrentMeasure_parityAvoid_eq_spinExpectation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {F : Finset (Sym2 V)}
-- given
  (hbeta : 0 ≤ beta)
  (hF : F ⊆ G.edgeFinset) :
-- imply
  (sourcelessCurrentMeasure G beta (fun _ => 1) hbeta (fun _ => zero_le_one) : Measure (EdgeCurrent G)) {m | Disjoint (currentParitySupport G m) F} = ENNReal.ofReal (((∑ s : ConfigSpace V, boltzmannJ G beta (fun _ => 1) s * Real.exp (-beta * edgeSpinSum F s)) / partitionJ G beta (fun _ => 1)) * Real.cosh beta ^ F.card) := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentMeasure_parityAvoid_eq_spinExpectation G beta hbeta F hF


-- created on 2026-10-23

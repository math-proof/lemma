import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.DecorationFormalMultiaffine
open StatMech StatMech.Onsager


/--
[ons_mvMonomialValue_scaleDecEdgeWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalMultiaffine.lean)
-/
@[path]
private lemma ons_mvMonomialValue_scaleDecEdgeWeight_eq
  {L : ℕ}
  {weight : ons_DecEdge L → ℂ}
  {edge : ons_DecEdge L}
  {t : ℂ}
  {m : ons_DecEdge L →₀ ℕ} :
-- imply
  ons_mvMonomialValue (ons_scaleDecEdgeWeight weight edge t) m = t ^ m edge * ons_mvMonomialValue weight m := by
-- proof
  apply StatMech.Onsager.ons_mvMonomialValue_scaleDecEdgeWeight weight edge t m

/--
[ons_MvSeriesEvalSummable_decFormalSecondDifference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalMultiaffine.lean)
-/
@[path]
private lemma ons_MvSeriesEvalSummable_decFormalSecondDifference_eq
  {L : ℕ}
  {series : MvPowerSeries (ons_DecEdge L) ℂ}
  {edge : ons_DecEdge L}
  {weight : ons_DecEdge L → ℂ}
-- given
  (h2 : ons_MvSeriesEvalSummable series (ons_scaleDecEdgeWeight weight edge 2))
  (h1 : ons_MvSeriesEvalSummable series weight)
  (h0 : ons_MvSeriesEvalSummable series (ons_scaleDecEdgeWeight weight edge 0)) :
-- imply
  ons_MvSeriesEvalSummable (ons_decFormalSecondDifference series edge) weight := by
-- proof
  apply StatMech.Onsager.ons_MvSeriesEvalSummable_decFormalSecondDifference series edge weight h2 h1 h0

/--
[ons_mvSeriesEval_decFormalSecondDifference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalMultiaffine.lean)
-/
@[path]
private lemma ons_mvSeriesEval_decFormalSecondDifference_eq
  {L : ℕ}
  {series : MvPowerSeries (ons_DecEdge L) ℂ}
  {edge : ons_DecEdge L}
  {weight : ons_DecEdge L → ℂ}
-- given
  (h2 : ons_MvSeriesEvalSummable series (ons_scaleDecEdgeWeight weight edge 2))
  (h1 : ons_MvSeriesEvalSummable series weight)
  (h0 : ons_MvSeriesEvalSummable series (ons_scaleDecEdgeWeight weight edge 0)) :
-- imply
  ons_mvSeriesEval (ons_decFormalSecondDifference series edge) weight = ons_mvSeriesEval series (ons_scaleDecEdgeWeight weight edge 2) - 2 * ons_mvSeriesEval series weight + ons_mvSeriesEval series (ons_scaleDecEdgeWeight weight edge 0) := by
-- proof
  apply StatMech.Onsager.ons_mvSeriesEval_decFormalSecondDifference series edge weight h2 h1 h0

/--
[norm_ons_scaleDecEdgeWeight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalMultiaffine.lean)
-/
@[path]
private lemma norm_ons_scaleDecEdgeWeight_le_eq
  {L : ℕ}
  {weight : ons_DecEdge L → ℂ}
  {edge : ons_DecEdge L}
  {t : ℂ}
  {r : ℝ}
  {f : ons_DecEdge L}
-- given
  (hr0 : 0 ≤ r)
  (ht : ‖t‖ ≤ 2)
  (hall : ∀ f, ‖weight f‖ ≤ r) :
-- imply
  ‖ons_scaleDecEdgeWeight weight edge t f‖ ≤ 2 * r := by
-- proof
  apply StatMech.Onsager.norm_ons_scaleDecEdgeWeight_le weight edge t r hr0 ht hall f

/--
[ons_detWalkRoot_scaleDecEdge_secondDifference_small](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalMultiaffine.lean)
-/
@[path]
private lemma ons_detWalkRoot_scaleDecEdge_secondDifference_small_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {edge : ons_DecEdge L}
  {r : ℝ}
-- given
  (hedge : edge ∈ (ons_decGraph L).edgeFinset)
  (hr : 0 < r)
  (hrOne : 2 * r ≤ 1)
  (hall : ∀ f, ‖decWeight f‖ ≤ r)
  (hsmallCompressed : 2 * r < (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹)
  (hsmallAugmented : 2 * r < (2 * (Fintype.card (ons_Dart L ⊕ Fin 2) : ℝ) ^ 2)⁻¹) :
-- imply
  ons_detWalkRoot (ons_KWmatDecorationWeightedPhase L (ons_scaleDecEdgeWeight decWeight edge 2) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) - 2 * ons_detWalkRoot (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) + ons_detWalkRoot (ons_KWmatDecorationWeightedPhase L (ons_scaleDecEdgeWeight decWeight edge 0) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = 0 := by
-- proof
  apply StatMech.Onsager.ons_detWalkRoot_scaleDecEdge_secondDifference_small L decWeight a b edge hedge r hr hrOne hall hsmallCompressed hsmallAugmented

/--
[ons_degreeFiberCoeff_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalMultiaffine.lean)
-/
@[path]
private lemma ons_degreeFiberCoeff_scale_eq
  [Fintype E]
  [DecidableEq E]
  {series : MvPowerSeries E ℂ}
  {weight : E → ℂ}
  {c : ℂ}
  {n : ℕ} :
-- imply
  ons_degreeFiberCoeff series (fun e ↦ c * weight e) n = c ^ n * ons_degreeFiberCoeff series weight n := by
-- proof
  apply StatMech.Onsager.ons_degreeFiberCoeff_scale series weight c n

/--
[ons_secondDifferenceFactor_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalMultiaffine.lean)
-/
@[path]
private lemma ons_secondDifferenceFactor_ne_zero_eq
  {k : ℕ}
-- given
  (hk : 2 ≤ k) :
-- imply
  ons_secondDifferenceFactor k ≠ 0 := by
-- proof
  apply StatMech.Onsager.ons_secondDifferenceFactor_ne_zero k hk

/--
[ons_decFormalRoot_coeff_eq_zero_of_repeated_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalMultiaffine.lean)
-/
@[path]
private lemma ons_decFormalRoot_coeff_eq_zero_of_repeated_mem_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {m : ons_DecEdge L →₀ ℕ}
  {edge : ons_DecEdge L}
-- given
  (hedge : edge ∈ (ons_decGraph L).edgeFinset)
  (hrepeated : 2 ≤ m edge) :
-- imply
  MvPowerSeries.coeff m (ons_decFormalRoot L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalRoot_coeff_eq_zero_of_repeated_mem L a b m edge hedge hrepeated

/--
[ons_decFormalRoot_coeff_eq_zero_of_repeated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalMultiaffine.lean)
-/
@[path]
private lemma ons_decFormalRoot_coeff_eq_zero_of_repeated_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {m : ons_DecEdge L →₀ ℕ}
  {edge : ons_DecEdge L}
-- given
  (hrepeated : 2 ≤ m edge) :
-- imply
  MvPowerSeries.coeff m (ons_decFormalRoot L ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decFormalRoot_coeff_eq_zero_of_repeated L a b m edge hrepeated

/--
[ons_DecFormalRepeatedEdgeVanishes_proved](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalMultiaffine.lean)
-/
@[path]
private lemma ons_DecFormalRepeatedEdgeVanishes_proved_eq :
-- imply
  ons_DecFormalRepeatedEdgeVanishes := by
-- proof
  apply StatMech.Onsager.ons_DecFormalRepeatedEdgeVanishes_proved

/--
[ons_free_energy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalMultiaffine.lean)
-/
@[path]
private lemma ons_free_energy_eq
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  Filter.Tendsto (ons_torusPressureSeq beta) Filter.atTop (nhds (ons_pressure beta)) := by
-- proof
  apply StatMech.Onsager.ons_free_energy beta hbeta

/--
[ons_free_energy_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalMultiaffine.lean)
-/
@[path]
private lemma ons_free_energy_unconditional_eq
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  Filter.Tendsto (ons_torusPressureSeq beta) Filter.atTop (nhds (ons_pressure beta)) := by
-- proof
  apply StatMech.Onsager.ons_free_energy_unconditional beta hbeta


-- created on 2026-10-23

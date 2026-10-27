import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWProbDualityClose.Part2
open Set MeasureTheory SimpleGraph StatMech StatMech.Universality


/--
[rpd_crossingPair_incompatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWProbDualityClose.lean)
-/
@[path]
private lemma rpd_crossingPair_incompatible_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  ¬ (ω e = true ∧ dualConfig ω (crossEdge e) = true) := by
-- proof
  apply StatMech.Universality.rpd_crossingPair_incompatible ω e

/--
[rpd_open_dualOpen_disjoint_crossPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWProbDualityClose.lean)
-/
@[path]
private lemma rpd_open_dualOpen_disjoint_crossPair_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)}
-- given
  (he : ω e = true) :
-- imply
  dualConfig ω (crossEdge e) = false := by
-- proof
  apply StatMech.Universality.rpd_open_dualOpen_disjoint_crossPair ω he

/--
[rpd_crossWalks_no_sharedCrossPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWProbDualityClose.lean)
-/
@[path]
private lemma rpd_crossWalks_no_sharedCrossPair_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
  {w : (openSubgraph 2 ω).Walk x y}
  {x' y' : Site 2}
  {w' : (openSubgraph 2 (dualConfig ω)).Walk x' y'}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ w.edges)
  (he' : crossEdge e ∈ w'.edges) :
-- imply
  False := by
-- proof
  apply StatMech.Universality.rpd_crossWalks_no_sharedCrossPair ω w w' e he he'

/--
[rpd_hCross_dualVCross_exclusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWProbDualityClose.lean)
-/
@[path]
private lemma rpd_hCross_dualVCross_exclusive_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {xh yh : Site 2}
  {wh : (openSubgraph 2 ω).Walk xh yh}
  {xv yv : Site 2}
  {wv : (openSubgraph 2 (dualConfig ω)).Walk xv yv}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ wh.edges)
  (he' : crossEdge e ∈ wv.edges) :
-- imply
  False := by
-- proof
  apply StatMech.Universality.rpd_hCross_dualVCross_exclusive ω wh wv e he he'

/--
[rpd_dualVerticalCrossing_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWProbDualityClose.lean)
-/
@[path]
private lemma rpd_dualVerticalCrossing_eq_eq
  {a b c d : ℤ}
-- given
  (hmeasV : MeasurableSet (verticalCrossingEvent a b c d)) :
-- imply
  rba_selfDualMeasure.real (dualVerticalCrossingEvent a b c d) = rba_selfDualMeasure.real (verticalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rpd_dualVerticalCrossing_eq a b c d hmeasV

/--
[rpd_square_reflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWProbDualityClose.lean)
-/
@[path]
private lemma rpd_square_reflection_eq
  {n : ℤ}
-- given
  (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n)) :
-- imply
  rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
-- proof
  apply StatMech.Universality.rpd_square_reflection n hmeasH

/--
[rpd_reindexInv_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWProbDualityClose.lean)
-/
@[path]
private lemma rpd_reindexInv_measurable_eq :
-- imply
  Measurable rpd_reindexInv := by
-- proof
  apply StatMech.Universality.rpd_reindexInv_measurable

/--
[rpd_map_reindexInv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWProbDualityClose.lean)
-/
@[path]
private lemma rpd_map_reindexInv_eq :
-- imply
  Measure.map rpd_reindexInv halfMeasure = halfMeasure := by
-- proof
  apply StatMech.Universality.rpd_map_reindexInv

/--
[rpd_reindexInv_dualConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWProbDualityClose.lean)
-/
@[path]
private lemma rpd_reindexInv_dualConfig_eq :
-- imply
  rpd_reindexInv ∘ dualConfig = (fun (η : ConfigSpace (Sym2 (Site 2))) e => !(η e)) := by
-- proof
  apply StatMech.Universality.rpd_reindexInv_dualConfig

/--
[rpd_selfDualDichotomy_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWProbDualityClose.lean)
-/
@[path]
private lemma rpd_selfDualDichotomy_nonvacuous_eq :
-- imply
  ∃ (H : Set (ConfigSpace (Sym2 (Site 2)))) (R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))), MeasurableSet H ∧ Measurable R ∧ Measure.map R halfMeasure = halfMeasure ∧ Hᶜ = (R ∘ dualConfig) ⁻¹' H := by
-- proof
  apply StatMech.Universality.rpd_selfDualDichotomy_nonvacuous

/--
[rpd_square_crossing_half_of_selfDualDichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWProbDualityClose.lean)
-/
@[path]
private lemma rpd_square_crossing_half_of_selfDualDichotomy_eq
  {n : ℤ}
  {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
-- given
  (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
  (hRmeas : Measurable R)
  (hRpres : Measure.map R halfMeasure = halfMeasure)
  (hdich : (horizontalCrossingEvent 0 n 0 n)ᶜ = (R ∘ dualConfig) ⁻¹' (horizontalCrossingEvent 0 n 0 n)) :
-- imply
  halfMeasure.real (horizontalCrossingEvent 0 n 0 n) = 1 / 2 := by
-- proof
  apply StatMech.Universality.rpd_square_crossing_half_of_selfDualDichotomy n hmeasH hRmeas hRpres hdich

/--
[rpd_square_crossing_le_and_ge_half_of_selfDualDichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWProbDualityClose.lean)
-/
@[path]
private lemma rpd_square_crossing_le_and_ge_half_of_selfDualDichotomy_eq
  {n : ℤ}
  {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
-- given
  (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
  (hRmeas : Measurable R)
  (hRpres : Measure.map R halfMeasure = halfMeasure)
  (hdich : (horizontalCrossingEvent 0 n 0 n)ᶜ = (R ∘ dualConfig) ⁻¹' (horizontalCrossingEvent 0 n 0 n)) :
-- imply
  halfMeasure.real (horizontalCrossingEvent 0 n 0 n) ≤ 1 / 2 ∧ (1 : ℝ) / 2 ≤ halfMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
-- proof
  apply StatMech.Universality.rpd_square_crossing_le_and_ge_half_of_selfDualDichotomy n hmeasH hRmeas hRpres hdich


-- created on 2026-10-23

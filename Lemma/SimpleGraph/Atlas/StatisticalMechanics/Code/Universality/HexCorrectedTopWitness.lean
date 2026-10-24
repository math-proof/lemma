import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexCorrectedTopWitness
open StatMech StatMech.Universality


/--
[hexCSTopWalkAtWidth_one_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedTopWitness.lean)
-/
@[path]
private lemma hexCSTopWalkAtWidth_one_nonempty_eq :
-- imply
  ∃ ts, HexCSTopWalkAtWidth 1 (by norm_num) ts := by
-- proof
  apply StatMech.Universality.hexCSTopWalkAtWidth_one_nonempty

/--
[hexCS_critical_divergence_of_recurrence_concrete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedTopWitness.lean)
-/
@[path]
private lemma hexCS_critical_divergence_of_recurrence_concrete_eq
-- given
  (hlocal : ∀ T L (hT : 0 < T), HexCSLocalRelation T L hT)
  (hwindow : ∀ T L (hT : 0 < T), HexCSBoundaryWindowLaw T L hT)
  (hrec : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE) → ∀ T, 1 ≤ T → hexCSInfiniteSideMassAtWidth (T + 1) - hexCSInfiniteSideMassAtWidth T ≤ hexChiE⁻¹ * (hexCSInfiniteTopMassAtWidth (T + 1)) ^ 2) :
-- imply
  ¬ Summable (fun n : ℕ => hlc_sawCountR hexAWStart 1 n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hexCS_critical_divergence_of_recurrence_concrete hlocal hwindow hrec

/--
[hexCS_critical_divergence_of_highestCuts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedTopWitness.lean)
-/
@[path]
private lemma hexCS_critical_divergence_of_highestCuts_eq
-- given
  (hlocal : ∀ T L (hT : 0 < T), HexCSLocalRelation T L hT)
  (hwindow : ∀ T L (hT : 0 < T), HexCSBoundaryWindowLaw T L hT)
  (HC : ∀ T (hT : 1 ≤ T), HexCSHighestCut T hT) :
-- imply
  ¬ Summable (fun n : ℕ => hlc_sawCountR hexAWStart 1 n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hexCS_critical_divergence_of_highestCuts hlocal hwindow HC


-- created on 2026-10-23

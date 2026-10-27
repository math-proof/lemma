import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedCriticalDivergence
open StatMech StatMech.Universality


/--
[hexCSInfiniteSideMassAtWidth_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedCriticalDivergence.lean)
-/
@[path]
private lemma hexCSInfiniteSideMassAtWidth_succ_eq
  {v : ℕ} :
-- imply
  hexCSInfiniteSideMassAtWidth (v + 1) = hexCSInfiniteSideMass v := by
-- proof
  apply StatMech.Universality.hexCSInfiniteSideMassAtWidth_succ v

/--
[hexCSInfiniteTopMassAtWidth_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedCriticalDivergence.lean)
-/
@[path]
private lemma hexCSInfiniteTopMassAtWidth_succ_eq
  {v : ℕ} :
-- imply
  hexCSInfiniteTopMassAtWidth (v + 1) = hexCSInfiniteTopMass v := by
-- proof
  apply StatMech.Universality.hexCSInfiniteTopMassAtWidth_succ v

/--
[hexCSInfiniteTopMassAtWidth_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedCriticalDivergence.lean)
-/
@[path]
private lemma hexCSInfiniteTopMassAtWidth_nonneg_eq
  {T : ℕ} :
-- imply
  0 ≤ hexCSInfiniteTopMassAtWidth T := by
-- proof
  apply StatMech.Universality.hexCSInfiniteTopMassAtWidth_nonneg T

/--
[hexCSInfiniteTopMassAtWidth_one_pos_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedCriticalDivergence.lean)
-/
@[path]
private lemma hexCSInfiniteTopMassAtWidth_one_pos_of_mem_eq
  {ts : List ℤ}
-- given
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE))
  (hts : HexCSTopWalkAtWidth 1 (by norm_num) ts) :
-- imply
  0 < hexCSInfiniteTopMassAtWidth 1 := by
-- proof
  apply StatMech.Universality.hexCSInfiniteTopMassAtWidth_one_pos_of_mem hwalk ts hts

/--
[hecd_correctedTop_columnSum_eq_atWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedCriticalDivergence.lean)
-/
@[path]
private lemma hecd_correctedTop_columnSum_eq_atWidth_eq
  {T : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hecd_columnSum hexAWStart 1 HexCSTopWalkAnyWidth hexCSTopWalkWidth T = hexCSInfiniteTopMassAtWidth T := by
-- proof
  apply StatMech.Universality.hecd_correctedTop_columnSum_eq_atWidth T hT

/--
[hexCS_infinite_height_identity_atWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedCriticalDivergence.lean)
-/
@[path]
private lemma hexCS_infinite_height_identity_atWidth_eq
  {T : ℕ}
-- given
  (hT : 0 < T)
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE))
  (hlocal : ∀ L, HexCSLocalRelation T L hT)
  (hwindow : ∀ L, HexCSBoundaryWindowLaw T L hT) :
-- imply
  hexCl * hexCSInfiniteSideMassAtWidth T + hexCSInfiniteTopMassAtWidth T = 1 := by
-- proof
  apply StatMech.Universality.hexCS_infinite_height_identity_atWidth T hT hwalk hlocal hwindow

/--
[hexCSInfiniteSideMassAtWidth_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedCriticalDivergence.lean)
-/
@[path]
private lemma hexCSInfiniteSideMassAtWidth_mono_eq
  {T : ℕ}
-- given
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE))
  (hT : 1 ≤ T) :
-- imply
  hexCSInfiniteSideMassAtWidth T ≤ hexCSInfiniteSideMassAtWidth (T + 1) := by
-- proof
  apply StatMech.Universality.hexCSInfiniteSideMassAtWidth_mono hwalk T hT

/--
[hexCS_critical_divergence_of_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedCriticalDivergence.lean)
-/
@[path]
private lemma hexCS_critical_divergence_of_recurrence_eq
-- given
  (hlocal : ∀ T L (hT : 0 < T), HexCSLocalRelation T L hT)
  (hwindow : ∀ T L (hT : 0 < T), HexCSBoundaryWindowLaw T L hT)
  (hrec : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE) → ∀ T, 1 ≤ T → hexCSInfiniteSideMassAtWidth (T + 1) - hexCSInfiniteSideMassAtWidth T ≤ hexChiE⁻¹ * (hexCSInfiniteTopMassAtWidth (T + 1)) ^ 2)
  (htopOne : ∃ ts, HexCSTopWalkAtWidth 1 (by norm_num) ts) :
-- imply
  ¬ Summable (fun n : ℕ => hlc_sawCountR hexAWStart 1 n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hexCS_critical_divergence_of_recurrence hlocal hwindow hrec htopOne


-- created on 2026-10-23

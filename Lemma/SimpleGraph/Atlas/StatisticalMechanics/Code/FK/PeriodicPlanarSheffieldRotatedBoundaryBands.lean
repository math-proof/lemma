import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRotatedBoundaryBands.Part2
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[siteAxisSwap_horizontalShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRotatedBoundaryBands.lean)
-/
@[path]
private lemma siteAxisSwap_horizontalShift_eq
  [DecidableEq V]
  [DecidableEq W]
  {t : Int} :
-- imply
  siteAxisSwap (horizontalShift t) = verticalShift t := by
-- proof
  apply StatMech.FK.PeriodicPlanar.siteAxisSwap_horizontalShift t

/--
[siteAxisSwap_verticalShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRotatedBoundaryBands.lean)
-/
@[path]
private lemma siteAxisSwap_verticalShift_eq
  [DecidableEq V]
  [DecidableEq W]
  {t : Int} :
-- imply
  siteAxisSwap (verticalShift t) = horizontalShift t := by
-- proof
  apply StatMech.FK.PeriodicPlanar.siteAxisSwap_verticalShift t

/--
[exists_pairedRotatedMixedBoundaryScores](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRotatedBoundaryBands.lean)
-/
@[path]
private lemma exists_pairedRotatedMixedBoundaryScores_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat → Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual) :
-- imply
  Nonempty (PairedMixedBoundaryScores E.axisSwap Edual.axisSwap mu muDual S Sdual p pDual) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_pairedRotatedMixedBoundaryScores E Edual mu muDual hTI hTIDual family familyDual schedule k


-- created on 2026-10-23

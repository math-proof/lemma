import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerron
open Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexEventuallyHasSymmetricBetheIdentification_of_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerron.lean)
-/
@[path]
private lemma sixVertexEventuallyHasSymmetricBetheIdentification_of_all_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (h : SixVertexHasSymmetricBetheIdentification c (sixVertexPositiveHalfBetheRootFamily hc)) :
-- imply
  SixVertexEventuallyHasSymmetricBetheIdentification hc := by
-- proof
  apply StatMech.FrontierD.sixVertexEventuallyHasSymmetricBetheIdentification_of_all hc h

/--
[sixVertexEventuallyHasSymmetricBetheIdentification_of_positivePhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerron.lean)
-/
@[path]
private lemma sixVertexEventuallyHasSymmetricBetheIdentification_of_positivePhase_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (hphase : SixVertexSelectedHalfFilledWaveHasPositivePhase c) :
-- imply
  SixVertexEventuallyHasSymmetricBetheIdentification hc := by
-- proof
  apply StatMech.FrontierD.sixVertexEventuallyHasSymmetricBetheIdentification_of_positivePhase hc hphase

/--
[sixVertexCentralWidthRate_eventuallyEq_candidateRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerron.lean)
-/
@[path]
private lemma sixVertexCentralWidthRate_eventuallyEq_candidateRate_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (hperron : SixVertexEventuallyHasSymmetricBetheIdentification hc) :
-- imply
  sixVertexCentralWidthRate c =ᶠ[atTop] sixVertexHalfFilledBetheCandidateRate hc := by
-- proof
  apply StatMech.FrontierD.sixVertexCentralWidthRate_eventuallyEq_candidateRate hc hperron

/--
[sixVertexBalanced_iteratedLimit_of_eventualPerron_of_rootDensityFourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerron.lean)
-/
@[path]
private lemma sixVertexBalanced_iteratedLimit_of_eventualPerron_of_rootDensityFourier_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (hperron : SixVertexEventuallyHasSymmetricBetheIdentification hc)
  (hbulk : SixVertexSelectedBulkMatchesRootDensityFourier hc) :
-- imply
  SixVertexHasIteratedLimit (sixVertexBalancedAreaDensity c) (sixVertexAntiferroelectricFreeEnergyValue (sixVertexAntiferroelectricLambda c)) := by
-- proof
  apply StatMech.FrontierD.sixVertexBalanced_iteratedLimit_of_eventualPerron_of_rootDensityFourier hc hperron hbulk


-- created on 2026-10-23

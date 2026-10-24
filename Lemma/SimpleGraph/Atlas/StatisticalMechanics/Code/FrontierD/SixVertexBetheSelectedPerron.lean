import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheSelectedPerron
open Finset Matrix StatMech StatMech.FrontierD


/--
[SixVertexSatisfiesMultiplicativeBetheEquations.physicalCoordinateBetheEigenrelation_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSelectedPerron.lean)
-/
@[path]
private lemma physicalCoordinateBetheEigenrelation_of_pos_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
-- given
  (hc : 2 < c)
  (hn : 0 < n)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N n p)
  (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1) :
-- imply
  SixVertexCoordinateBetheEigenrelation (N := N) c p := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.physicalCoordinateBetheEigenrelation_of_pos hc hn p hp hphase

/--
[sixVertexHalfFilledBetheRoots_physicalEigenrelation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSelectedPerron.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheRoots_physicalEigenrelation_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexCoordinateBetheEigenrelation (N := sixVertexFourWidth 0 k) c (sixVertexHalfFilledBetheRoots hc k) := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheRoots_physicalEigenrelation hc k

/--
[sixVertexHalfFilledBetheRealWave_eigenrelation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSelectedPerron.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheRealWave_eigenrelation_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexSectorTransfer (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) c *ᵥ sixVertexHalfFilledBetheRealWave hc k = sixVertexSymmetricBetheEigenvalueValue c (sixVertexPositiveHalfBetheRoots hc k) • sixVertexHalfFilledBetheRealWave hc k := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheRealWave_eigenrelation hc k

/--
[sixVertexHasSymmetricBetheIdentification_of_selectedWavePositive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSelectedPerron.lean)
-/
@[path]
private lemma sixVertexHasSymmetricBetheIdentification_of_selectedWavePositive_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (hpos : SixVertexSelectedHalfFilledWavePositive c) :
-- imply
  SixVertexHasSymmetricBetheIdentification c (sixVertexPositiveHalfBetheRootFamily hc) := by
-- proof
  apply StatMech.FrontierD.sixVertexHasSymmetricBetheIdentification_of_selectedWavePositive hc hpos


-- created on 2026-10-23

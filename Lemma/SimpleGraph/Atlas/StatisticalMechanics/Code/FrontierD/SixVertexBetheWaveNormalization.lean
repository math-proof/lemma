import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheWaveNormalization
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexCoordinateBetheWave_two_packed_eq_phase_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWaveNormalization.lean)
-/
@[path]
private lemma sixVertexCoordinateBetheWave_two_packed_eq_phase_sub_eq
  {c : Real}
  {p : Fin 2 → Real}
-- given
  (hsymm : ∀ j, p j.rev = -p j) :
-- imply
  sixVertexCoordinateBetheWave (N := 4) c p (sixVertexPackedSector 4 2 (by omega)) = 2 * (sixVertexBethePhase (p 1) - sixVertexBethePhase (p 0)) := by
-- proof
  apply StatMech.FrontierD.sixVertexCoordinateBetheWave_two_packed_eq_phase_sub hsymm

/--
[sixVertexCoordinateBetheWave_two_packed_re_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWaveNormalization.lean)
-/
@[path]
private lemma sixVertexCoordinateBetheWave_two_packed_re_eq_zero_eq
  {c : Real}
  {p : Fin 2 → Real}
-- given
  (hsymm : ∀ j, p j.rev = -p j) :
-- imply
  (sixVertexCoordinateBetheWave (N := 4) c p (sixVertexPackedSector 4 2 (by omega))).re = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexCoordinateBetheWave_two_packed_re_eq_zero hsymm

/--
[sixVertexHalfFilledBetheRealWave_zero_at_width_four_packed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWaveNormalization.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheRealWave_zero_at_width_four_packed_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexHalfFilledBetheRealWave hc 0 (sixVertexPackedSector 4 2 (by omega)) = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheRealWave_zero_at_width_four_packed hc

/--
[not_sixVertexSelectedHalfFilledWavePositive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWaveNormalization.lean)
-/
@[path]
private lemma not_sixVertexSelectedHalfFilledWavePositive_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  ¬ SixVertexSelectedHalfFilledWavePositive c := by
-- proof
  apply StatMech.FrontierD.not_sixVertexSelectedHalfFilledWavePositive hc

/--
[sixVertexPositiveHalfBetheRoots_quantile_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWaveNormalization.lean)
-/
@[path]
private lemma sixVertexPositiveHalfBetheRoots_quantile_lower_eq
  {c : Real}
  {k : Nat}
  {j : Fin (k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  Real.pi * (2 * (j : Real) + 1) < (sixVertexFourWidth 0 k : Real) * sixVertexPositiveHalfBetheRoots hc k j := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveHalfBetheRoots_quantile_lower hc k j

/--
[sixVertexHalfFilledBetheRotatedRealWave_eigenrelation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWaveNormalization.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheRotatedRealWave_eigenrelation_eq
  {c : Real}
  {k : Nat}
  {a : Complex}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexSectorTransfer (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) c *ᵥ sixVertexHalfFilledBetheRotatedRealWave hc k a = sixVertexSymmetricBetheEigenvalueValue c (sixVertexPositiveHalfBetheRoots hc k) • sixVertexHalfFilledBetheRotatedRealWave hc k a := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheRotatedRealWave_eigenrelation hc k a

/--
[sixVertexHasSymmetricBetheIdentification_of_selectedWaveHasPositivePhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWaveNormalization.lean)
-/
@[path]
private lemma sixVertexHasSymmetricBetheIdentification_of_selectedWaveHasPositivePhase_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (hpos : SixVertexSelectedHalfFilledWaveHasPositivePhase c) :
-- imply
  SixVertexHasSymmetricBetheIdentification c (sixVertexPositiveHalfBetheRootFamily hc) := by
-- proof
  apply StatMech.FrontierD.sixVertexHasSymmetricBetheIdentification_of_selectedWaveHasPositivePhase hc hpos

/--
[sixVertexHalfFilledBethePhaseCorrectedWaveTwo_packed_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWaveNormalization.lean)
-/
@[path]
private lemma sixVertexHalfFilledBethePhaseCorrectedWaveTwo_packed_pos_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexHalfFilledBethePhaseCorrectedWaveTwo hc (sixVertexPackedSector 4 2 (by omega)) := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBethePhaseCorrectedWaveTwo_packed_pos hc

/--
[sixVertexHalfFilledBethePhaseCorrectedWaveTwo_eigenrelation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWaveNormalization.lean)
-/
@[path]
private lemma sixVertexHalfFilledBethePhaseCorrectedWaveTwo_eigenrelation_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexSectorTransfer 4 2 c *ᵥ sixVertexHalfFilledBethePhaseCorrectedWaveTwo hc = sixVertexSymmetricBetheEigenvalueValue c (sixVertexPositiveHalfBetheRoots hc 0) • sixVertexHalfFilledBethePhaseCorrectedWaveTwo hc := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBethePhaseCorrectedWaveTwo_eigenrelation hc


-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalization.Part2
open StatMech StatMech.Universality


/--
[hexChi_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalization.lean)
-/
@[path]
private lemma hexChi_ne_one_eq :
-- imply
  hexChi ≠ 1 := by
-- proof
  apply StatMech.Universality.hexChi_ne_one

/--
[hexVBC_start_observable_eq_hexChi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalization.lean)
-/
@[path]
private lemma hexVBC_start_observable_eq_hexChi_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  parafObservable (hexVBCRegion a h0).inRegion a h0 a (5 / 8) hexChi = (hexChi : ℂ) := by
-- proof
  apply StatMech.Universality.hexVBC_start_observable_eq_hexChi a h0

/--
[hexVBC_start_observable_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalization.lean)
-/
@[path]
private lemma hexVBC_start_observable_ne_one_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  parafObservable (hexVBCRegion a h0).inRegion a h0 a (5 / 8) hexChi ≠ (1 : ℂ) := by
-- proof
  apply StatMech.Universality.hexVBC_start_observable_ne_one a h0

/--
[hexVBC_normalized_start_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalization.lean)
-/
@[path]
private lemma hexVBC_normalized_start_eq_one_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  normalizedParafObservable (hexVBCRegion a h0).inRegion a h0 a (5 / 8) hexChi = 1 := by
-- proof
  apply StatMech.Universality.hexVBC_normalized_start_eq_one a h0

/--
[hexVBC_boundaryData_Fa_eq_hexChi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalization.lean)
-/
@[path]
private lemma hexVBC_boundaryData_Fa_eq_hexChi_eq
  [DecidableEq V]
  {a : ℂ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {B : HexFiniteStripBoundaryData (hexVBCRegion a h0) h0 D P}
-- given
  (h0 : ℤ) :
-- imply
  B.Fa = hexChi := by
-- proof
  apply StatMech.Universality.hexVBC_boundaryData_Fa_eq_hexChi a h0 D P B

/--
[hexVBC_boundaryData_Fa_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalization.lean)
-/
@[path]
private lemma hexVBC_boundaryData_Fa_ne_one_eq
  [DecidableEq V]
  {a : ℂ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {B : HexFiniteStripBoundaryData (hexVBCRegion a h0) h0 D P}
-- given
  (h0 : ℤ) :
-- imply
  B.Fa ≠ 1 := by
-- proof
  apply StatMech.Universality.hexVBC_boundaryData_Fa_ne_one a h0 D P B


-- created on 2026-10-23

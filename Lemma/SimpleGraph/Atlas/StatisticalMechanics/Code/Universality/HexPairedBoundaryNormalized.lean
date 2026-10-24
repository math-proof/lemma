import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexPairedBoundaryNormalized
open StatMech StatMech.Universality StatMech.Universality.HexFiniteStripMirrorPairedData


/--
[normalized_pairedContribution_decompose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairedBoundaryNormalized.lean)
-/
@[path]
private lemma normalized_pairedContribution_decompose_eq
  [Fintype ι]
  [DecidableEq ι]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
  {K : DCSClassification H}
-- given
  (H : HexFiniteStripMirrorPairedData (ι := ι) C) :
-- imply
  hexChi⁻¹ * H.pairedContribution = hexCl * dcsLam H K + hexCt * dcsTau H K + dcsUps H K := by
-- proof
  apply StatMech.Universality.HexFiniteStripMirrorPairedData.normalized_pairedContribution_decompose H K

/--
[normalized_dcs_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairedBoundaryNormalized.lean)
-/
@[path]
private lemma normalized_dcs_identity_eq
  [Fintype ι]
  [DecidableEq ι]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
  {K : DCSClassification H}
-- given
  (H : HexFiniteStripMirrorPairedData (ι := ι) C) :
-- imply
  hexCl * dcsLam H K + hexCt * dcsTau H K + dcsUps H K = 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripMirrorPairedData.normalized_dcs_identity H K


-- created on 2026-10-23

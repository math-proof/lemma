import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexMirrorPairedBoundary
open StatMech StatMech.Universality StatMech.Universality.HexMirrorBoundaryPair StatMech.Universality.HexFiniteStripMirrorPairedData


/--
[unit_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairedBoundary.lean)
-/
@[path]
private lemma unit_projection_eq
  [DecidableEq V]
  {D : HexDomain V}
  {heading : V → Fin 3 → ℤ}
  {Q : HexMirrorBoundaryPair D heading} :
-- imply
  (∑ e ∈ Q.piece, hexUnit (heading e.vtx e.edge) * D.obs (D.mid e.vtx e.edge)) = Complex.I * ((2 * Real.cos Q.angle * Q.mass : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.HexMirrorBoundaryPair.unit_projection Q

/--
[pair_incTerm_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairedBoundary.lean)
-/
@[path]
private lemma pair_incTerm_sum_eq
  [Fintype ι]
  [DecidableEq ι]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
  {i : ι}
-- given
  (H : HexFiniteStripMirrorPairedData (ι := ι) C) :
-- imply
  (∑ e ∈ (H.pairs i).piece, D.incTerm e) = (1 / 2 : ℂ) * Complex.I * ((2 * Real.cos (H.pairs i).angle * (H.pairs i).mass : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.HexFiniteStripMirrorPairedData.pair_incTerm_sum H i

/--
[start_incTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairedBoundary.lean)
-/
@[path]
private lemma start_incTerm_eq
  [Fintype ι]
  [DecidableEq ι]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
-- given
  (H : HexFiniteStripMirrorPairedData (ι := ι) C) :
-- imply
  D.incTerm H.startIncidence = -(1 / 2 : ℂ) * Complex.I * (C.Fa : ℂ) := by
-- proof
  apply StatMech.Universality.HexFiniteStripMirrorPairedData.start_incTerm H

/--
[boundarySum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairedBoundary.lean)
-/
@[path]
private lemma boundarySum_eq_eq
  [Fintype ι]
  [DecidableEq ι]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
-- given
  (H : HexFiniteStripMirrorPairedData (ι := ι) C) :
-- imply
  D.boundarySum P = (1 / 2 : ℂ) * Complex.I * ((H.pairedContribution - C.Fa : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.HexFiniteStripMirrorPairedData.boundarySum_eq H

/--
[pairedContribution_eq_Fa](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairedBoundary.lean)
-/
@[path]
private lemma pairedContribution_eq_Fa_eq
  [Fintype ι]
  [DecidableEq ι]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
-- given
  (H : HexFiniteStripMirrorPairedData (ι := ι) C) :
-- imply
  H.pairedContribution = C.Fa := by
-- proof
  apply StatMech.Universality.HexFiniteStripMirrorPairedData.pairedContribution_eq_Fa H

/--
[normalized_real_boundary_contribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairedBoundary.lean)
-/
@[path]
private lemma normalized_real_boundary_contribution_eq
  [Fintype ι]
  [DecidableEq ι]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
-- given
  (H : HexFiniteStripMirrorPairedData (ι := ι) C) :
-- imply
  hexChi⁻¹ * H.pairedContribution = 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripMirrorPairedData.normalized_real_boundary_contribution H

/--
[hexGenuineStrip_mirrorPaired_normalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairedBoundary.lean)
-/
@[path]
private lemma hexGenuineStrip_mirrorPaired_normalized_eq :
-- imply
  hexChi⁻¹ * hexGenuineStripMirrorPairedData.pairedContribution = 1 := by
-- proof
  apply StatMech.Universality.hexGenuineStrip_mirrorPaired_normalized


-- created on 2026-10-23

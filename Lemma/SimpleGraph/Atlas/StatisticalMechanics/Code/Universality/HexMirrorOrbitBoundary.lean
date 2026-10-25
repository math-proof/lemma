import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3
open StatMech StatMech.Universality StatMech.Universality.HexFixedBoundaryPoint StatMech.Universality.HexFiniteStripMirrorOrbitData


/--
[unit_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorOrbitBoundary.lean)
-/
@[path]
private lemma unit_projection_eq
  [DecidableEq V]
  {D : HexDomain V}
  {heading : V → Fin 3 → ℤ}
  {Q : HexFixedBoundaryPoint D heading} :
-- imply
  (∑ e ∈ Q.piece, hexUnit (heading e.vtx e.edge) * D.obs (D.mid e.vtx e.edge)) = Complex.I * (Q.mass : ℂ) := by
-- proof
  apply StatMech.Universality.HexFixedBoundaryPoint.unit_projection Q

/--
[boundarySum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorOrbitBoundary.lean)
-/
@[path]
private lemma boundarySum_eq_eq
  [Fintype I]
  [Fintype K]
  [DecidableEq I]
  [DecidableEq K]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
-- given
  (H : HexFiniteStripMirrorOrbitData (I := I) (K := K) C) :
-- imply
  D.boundarySum P = (1 / 2 : ℂ) * Complex.I * ((H.totalContribution - C.Fa : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.HexFiniteStripMirrorOrbitData.boundarySum_eq H

/--
[totalContribution_eq_Fa](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorOrbitBoundary.lean)
-/
@[path]
private lemma totalContribution_eq_Fa_eq
  [Fintype I]
  [Fintype K]
  [DecidableEq I]
  [DecidableEq K]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
-- given
  (H : HexFiniteStripMirrorOrbitData (I := I) (K := K) C) :
-- imply
  H.totalContribution = C.Fa := by
-- proof
  apply StatMech.Universality.HexFiniteStripMirrorOrbitData.totalContribution_eq_Fa H

/--
[normalized_totalContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorOrbitBoundary.lean)
-/
@[path]
private lemma normalized_totalContribution_eq
  [Fintype I]
  [Fintype K]
  [DecidableEq I]
  [DecidableEq K]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
-- given
  (H : HexFiniteStripMirrorOrbitData (I := I) (K := K) C) :
-- imply
  hexChi⁻¹ * H.totalContribution = 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripMirrorOrbitData.normalized_totalContribution H

/--
[pairClassMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorOrbitBoundary.lean)
-/
@[path]
private lemma pairClassMass_nonneg_eq
  [Fintype I]
  [Fintype K]
  [DecidableEq I]
  [DecidableEq K]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
  {Kc : DCSClassification H}
  {k : HexPairedBoundaryClass}
-- given
  (H : HexFiniteStripMirrorOrbitData (I := I) (K := K) C)
  (hpairs : ∀ i, 0 ≤ (H.pairs i).mass) :
-- imply
  0 ≤ H.pairClassMass Kc k := by
-- proof
  apply StatMech.Universality.HexFiniteStripMirrorOrbitData.pairClassMass_nonneg H Kc hpairs k

/--
[fixedMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorOrbitBoundary.lean)
-/
@[path]
private lemma fixedMass_nonneg_eq
  [Fintype I]
  [Fintype K]
  [DecidableEq I]
  [DecidableEq K]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
  {Kc : DCSClassification H}
-- given
  (H : HexFiniteStripMirrorOrbitData (I := I) (K := K) C) :
-- imply
  0 ≤ H.fixedMass := by
-- proof
  apply StatMech.Universality.HexFiniteStripMirrorOrbitData.fixedMass_nonneg H Kc

/--
[normalized_class_values_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorOrbitBoundary.lean)
-/
@[path]
private lemma normalized_class_values_nonneg_eq
  [Fintype I]
  [Fintype K]
  [DecidableEq I]
  [DecidableEq K]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
  {Kc : DCSClassification H}
-- given
  (H : HexFiniteStripMirrorOrbitData (I := I) (K := K) C)
  (hpairs : ∀ i, 0 ≤ (H.pairs i).mass) :
-- imply
  0 ≤ H.dcsLam Kc ∧ 0 ≤ H.dcsTau Kc ∧ 0 ≤ H.dcsUps Kc := by
-- proof
  apply StatMech.Universality.HexFiniteStripMirrorOrbitData.normalized_class_values_nonneg H Kc hpairs

/--
[normalized_totalContribution_decompose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorOrbitBoundary.lean)
-/
@[path]
private lemma normalized_totalContribution_decompose_eq
  [Fintype I]
  [Fintype K]
  [DecidableEq I]
  [DecidableEq K]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
  {Kc : DCSClassification H}
-- given
  (H : HexFiniteStripMirrorOrbitData (I := I) (K := K) C) :
-- imply
  hexChi⁻¹ * H.totalContribution = hexCl * H.dcsLam Kc + hexCt * H.dcsTau Kc + H.dcsUps Kc := by
-- proof
  apply StatMech.Universality.HexFiniteStripMirrorOrbitData.normalized_totalContribution_decompose H Kc

/--
[normalized_dcs_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorOrbitBoundary.lean)
-/
@[path]
private lemma normalized_dcs_identity_eq
  [Fintype I]
  [Fintype K]
  [DecidableEq I]
  [DecidableEq K]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
  {Kc : DCSClassification H}
-- given
  (H : HexFiniteStripMirrorOrbitData (I := I) (K := K) C) :
-- imply
  hexCl * H.dcsLam Kc + hexCt * H.dcsTau Kc + H.dcsUps Kc = 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripMirrorOrbitData.normalized_dcs_identity H Kc


-- created on 2026-10-23

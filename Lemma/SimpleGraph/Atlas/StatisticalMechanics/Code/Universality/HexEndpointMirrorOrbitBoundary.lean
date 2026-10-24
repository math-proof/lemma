import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary
open StatMech StatMech.Universality StatMech.Universality.HexEndpointMirrorOrbitData


/--
[endpointMirrorBoundaryPair_mass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointMirrorOrbitBoundary.lean)
-/
@[path]
private lemma endpointMirrorBoundaryPair_mass_nonneg_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {eNeg ePos : HexIncidence V}
  {W : ℝ}
-- given
  (heading : V → Fin 3 → ℤ)
  (hobs : ∀ z, D.obs z = endpointParafObservable R.inRegion R.start h0 z (5 / 8) hexChi)
  (hne : eNeg ≠ ePos)
  (headNeg headPos : ℤ)
  (hHeadNeg : heading eNeg.vtx eNeg.edge = headNeg)
  (hHeadPos : heading ePos.vtx ePos.edge = headPos)
  (hmidPos : D.mid ePos.vtx ePos.edge = hsc_refl R.start h0 (D.mid eNeg.vtx eNeg.edge))
  (hsym : ∀ m, R.inRegion m → R.inRegion (hsc_refl R.start h0 m))
  (hdetNeg : ∀ ts, (ofTurns R.start h0 ts).EndpointIsLegalSAW ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion ∧ (ofTurns R.start h0 ts).EndsAt (D.mid eNeg.vtx eNeg.edge) → (ofTurns R.start h0 ts).turning = W)
  (htilt : hexPhase_sideTilt headPos = -hexPhase_sideTilt headNeg) :
-- imply
  0 ≤ (endpointMirrorBoundaryPair_of_reflection heading hobs eNeg ePos hne headNeg headPos hHeadNeg hHeadPos hmidPos hsym W hdetNeg htilt).mass := by
-- proof
  apply StatMech.Universality.endpointMirrorBoundaryPair_mass_nonneg heading hobs eNeg ePos hne headNeg headPos hHeadNeg hHeadPos hmidPos hsym W hdetNeg htilt

/--
[boundarySum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointMirrorOrbitBoundary.lean)
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
  {C : HexEndpointBoundaryCore R h0 D P}
-- given
  (H : HexEndpointMirrorOrbitData (I := I) (K := K) C) :
-- imply
  D.boundarySum P = (1 / 2 : ℂ) * Complex.I * ((H.totalContribution - 1 : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.HexEndpointMirrorOrbitData.boundarySum_eq H

/--
[totalContribution_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointMirrorOrbitBoundary.lean)
-/
@[path]
private lemma totalContribution_eq_one_eq
  [Fintype I]
  [Fintype K]
  [DecidableEq I]
  [DecidableEq K]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexEndpointBoundaryCore R h0 D P}
-- given
  (H : HexEndpointMirrorOrbitData (I := I) (K := K) C) :
-- imply
  H.totalContribution = 1 := by
-- proof
  apply StatMech.Universality.HexEndpointMirrorOrbitData.totalContribution_eq_one H

/--
[pairClassMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointMirrorOrbitBoundary.lean)
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
  {C : HexEndpointBoundaryCore R h0 D P}
  {Kc : DCSClassification H}
  {k : HexPairedBoundaryClass}
-- given
  (H : HexEndpointMirrorOrbitData (I := I) (K := K) C)
  (hpairs : ∀ i, 0 ≤ (H.pairs i).mass) :
-- imply
  0 ≤ H.pairClassMass Kc k := by
-- proof
  apply StatMech.Universality.HexEndpointMirrorOrbitData.pairClassMass_nonneg H Kc hpairs k

/--
[fixedMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointMirrorOrbitBoundary.lean)
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
  {C : HexEndpointBoundaryCore R h0 D P}
  {Kc : DCSClassification H}
-- given
  (H : HexEndpointMirrorOrbitData (I := I) (K := K) C) :
-- imply
  0 ≤ H.fixedMass := by
-- proof
  apply StatMech.Universality.HexEndpointMirrorOrbitData.fixedMass_nonneg H Kc

/--
[dcs_values_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointMirrorOrbitBoundary.lean)
-/
@[path]
private lemma dcs_values_nonneg_eq
  [Fintype I]
  [Fintype K]
  [DecidableEq I]
  [DecidableEq K]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexEndpointBoundaryCore R h0 D P}
  {Kc : DCSClassification H}
-- given
  (H : HexEndpointMirrorOrbitData (I := I) (K := K) C)
  (hpairs : ∀ i, 0 ≤ (H.pairs i).mass) :
-- imply
  0 ≤ H.dcsLam Kc ∧ 0 ≤ H.dcsTau Kc ∧ 0 ≤ H.dcsUps Kc := by
-- proof
  apply StatMech.Universality.HexEndpointMirrorOrbitData.dcs_values_nonneg H Kc hpairs

/--
[totalContribution_decompose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointMirrorOrbitBoundary.lean)
-/
@[path]
private lemma totalContribution_decompose_eq
  [Fintype I]
  [Fintype K]
  [DecidableEq I]
  [DecidableEq K]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexEndpointBoundaryCore R h0 D P}
  {Kc : DCSClassification H}
-- given
  (H : HexEndpointMirrorOrbitData (I := I) (K := K) C) :
-- imply
  H.totalContribution = hexCl * H.dcsLam Kc + hexCt * H.dcsTau Kc + H.dcsUps Kc := by
-- proof
  apply StatMech.Universality.HexEndpointMirrorOrbitData.totalContribution_decompose H Kc

/--
[normalized_dcs_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointMirrorOrbitBoundary.lean)
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
  {C : HexEndpointBoundaryCore R h0 D P}
  {Kc : DCSClassification H}
-- given
  (H : HexEndpointMirrorOrbitData (I := I) (K := K) C) :
-- imply
  hexCl * H.dcsLam Kc + hexCt * H.dcsTau Kc + H.dcsUps Kc = 1 := by
-- proof
  apply StatMech.Universality.HexEndpointMirrorOrbitData.normalized_dcs_identity H Kc


-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorPairFromReflection.Part5
open StatMech StatMech.Universality StatMech.Universality.HexFiniteStripReflectedPairing


/--
[hexPhase_sideTilt_reflect_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairFromReflection.lean)
-/
@[path]
private lemma hexPhase_sideTilt_reflect_one_eq
-- given
  (h : ℤ) :
-- imply
  hexPhase_sideTilt (2 - h) = -hexPhase_sideTilt h := by
-- proof
  apply StatMech.Universality.hexPhase_sideTilt_reflect_one h

/--
[hexMirrorBoundaryPair_of_reflection_angle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairFromReflection.lean)
-/
@[path]
private lemma hexMirrorBoundaryPair_of_reflection_angle_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
  {eNeg ePos : HexIncidence V}
  {W : ℝ}
-- given
  (heading : V → Fin 3 → ℤ)
  (hne : eNeg ≠ ePos)
  (headNeg headPos : ℤ)
  (hHeadNeg : heading eNeg.vtx eNeg.edge = headNeg)
  (hHeadPos : heading ePos.vtx ePos.edge = headPos)
  (hmidPos : D.mid ePos.vtx ePos.edge = hsc_refl R.start h0 (D.mid eNeg.vtx eNeg.edge))
  (hsym : ∀ m, R.inRegion m → R.inRegion (hsc_refl R.start h0 m))
  (hdetNeg : ∀ ts, (ofTurns R.start h0 ts).IsLegalSAW ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion ∧ (ofTurns R.start h0 ts).EndsAt (D.mid eNeg.vtx eNeg.edge) → (ofTurns R.start h0 ts).turning = W)
  (htilt : hexPhase_sideTilt headPos = -hexPhase_sideTilt headNeg) :
-- imply
  (hexMirrorBoundaryPair_of_reflection C heading eNeg ePos hne headNeg headPos hHeadNeg hHeadPos hmidPos hsym W hdetNeg htilt).angle = hexPhase_sideTilt headNeg + (5 / 8 : ℝ) * W := by
-- proof
  apply StatMech.Universality.hexMirrorBoundaryPair_of_reflection_angle C heading eNeg ePos hne headNeg headPos hHeadNeg hHeadPos hmidPos hsym W hdetNeg htilt

/--
[pair_piece](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairFromReflection.lean)
-/
@[path]
private lemma pair_piece_eq
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
  (S : HexFiniteStripReflectedPairing (ι := ι) C) :
-- imply
  (S.pair i).piece = {S.neg i, S.pos i} := by
-- proof
  apply StatMech.Universality.HexFiniteStripReflectedPairing.pair_piece S i

/--
[pair_mass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairFromReflection.lean)
-/
@[path]
private lemma pair_mass_nonneg_eq
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
  (S : HexFiniteStripReflectedPairing (ι := ι) C) :
-- imply
  0 ≤ (S.pair i).mass := by
-- proof
  apply StatMech.Universality.HexFiniteStripReflectedPairing.pair_mass_nonneg S i

/--
[toMirrorPairedData_pair_angle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairFromReflection.lean)
-/
@[path]
private lemma toMirrorPairedData_pair_angle_eq
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
  (S : HexFiniteStripReflectedPairing (ι := ι) C) :
-- imply
  ((S.toMirrorPairedData).pairs i).angle = hexPhase_sideTilt (S.headNeg i) + (5 / 8 : ℝ) * S.winding i := by
-- proof
  apply StatMech.Universality.HexFiniteStripReflectedPairing.toMirrorPairedData_pair_angle S i

/--
[classMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairFromReflection.lean)
-/
@[path]
private lemma classMass_nonneg_eq
  [Fintype ι]
  [DecidableEq ι]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
  {A : DCSAngles S}
  {k : HexPairedBoundaryClass}
-- given
  (S : HexFiniteStripReflectedPairing (ι := ι) C) :
-- imply
  0 ≤ HexFiniteStripMirrorPairedData.classMass S.toMirrorPairedData (A.toClassification S) k := by
-- proof
  apply StatMech.Universality.HexFiniteStripReflectedPairing.classMass_nonneg S A k

/--
[classMass_pos_of_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairFromReflection.lean)
-/
@[path]
private lemma classMass_pos_of_pair_eq
  [Fintype ι]
  [DecidableEq ι]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
  {A : DCSAngles S}
  {k : HexPairedBoundaryClass}
  {i : ι}
-- given
  (S : HexFiniteStripReflectedPairing (ι := ι) C)
  (hik : A.classOf i = k)
  (hi : 0 < (S.pair i).mass) :
-- imply
  0 < HexFiniteStripMirrorPairedData.classMass S.toMirrorPairedData (A.toClassification S) k := by
-- proof
  apply StatMech.Universality.HexFiniteStripReflectedPairing.classMass_pos_of_pair S A k i hik hi

/--
[normalized_class_value_pos_of_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairFromReflection.lean)
-/
@[path]
private lemma normalized_class_value_pos_of_pair_eq
  [Fintype ι]
  [DecidableEq ι]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
  {A : DCSAngles S}
  {k : HexPairedBoundaryClass}
  {i : ι}
-- given
  (S : HexFiniteStripReflectedPairing (ι := ι) C)
  (hik : A.classOf i = k)
  (hi : 0 < (S.pair i).mass) :
-- imply
  0 < hexChi⁻¹ * HexFiniteStripMirrorPairedData.classMass S.toMirrorPairedData (A.toClassification S) k := by
-- proof
  apply StatMech.Universality.HexFiniteStripReflectedPairing.normalized_class_value_pos_of_pair S A k i hik hi

/--
[normalized_class_values_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairFromReflection.lean)
-/
@[path]
private lemma normalized_class_values_nonneg_eq
  [Fintype ι]
  [DecidableEq ι]
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
  {A : DCSAngles S}
-- given
  (S : HexFiniteStripReflectedPairing (ι := ι) C) :
-- imply
  0 ≤ HexFiniteStripMirrorPairedData.dcsLam S.toMirrorPairedData (A.toClassification S) ∧ 0 ≤ HexFiniteStripMirrorPairedData.dcsTau S.toMirrorPairedData (A.toClassification S) ∧ 0 ≤ HexFiniteStripMirrorPairedData.dcsUps S.toMirrorPairedData (A.toClassification S) := by
-- proof
  apply StatMech.Universality.HexFiniteStripReflectedPairing.normalized_class_values_nonneg S A

/--
[normalized_dcs_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairFromReflection.lean)
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
  {A : DCSAngles S}
-- given
  (S : HexFiniteStripReflectedPairing (ι := ι) C) :
-- imply
  hexCl * HexFiniteStripMirrorPairedData.dcsLam S.toMirrorPairedData (A.toClassification S) + hexCt * HexFiniteStripMirrorPairedData.dcsTau S.toMirrorPairedData (A.toClassification S) + HexFiniteStripMirrorPairedData.dcsUps S.toMirrorPairedData (A.toClassification S) = 1 := by
-- proof
  apply StatMech.Universality.HexFiniteStripReflectedPairing.normalized_dcs_identity S A


-- created on 2026-10-23

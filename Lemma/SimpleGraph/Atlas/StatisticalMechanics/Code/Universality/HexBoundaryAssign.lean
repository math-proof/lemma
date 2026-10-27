import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
open StatMech StatMech.Universality StatMech.Universality.HexRegionAssign


/--
[hexRegionCls_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean)
-/
@[path]
private lemma hexRegionCls_start_eq
  {R : HexRegion} :
-- imply
  hexRegionCls R R.start = 0 := by
-- proof
  apply StatMech.Universality.hexRegionCls_start R

/--
[hexRegionCls_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean)
-/
@[path]
private lemma hexRegionCls_left_eq
  {R : HexRegion}
  {z : ℂ}
-- given
  (hz : z.re = 0)
  (hne : z ≠ R.start) :
-- imply
  hexRegionCls R z = 1 := by
-- proof
  apply StatMech.Universality.hexRegionCls_left R hz hne

/--
[hexRegionCls_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean)
-/
@[path]
private lemma hexRegionCls_right_eq
  {R : HexRegion}
  {z : ℂ}
-- given
  (hz : z.re = R.width)
  (hne : z ≠ R.start)
  (hl : z.re ≠ 0) :
-- imply
  hexRegionCls R z = 4 := by
-- proof
  apply StatMech.Universality.hexRegionCls_right R hz hne hl

/--
[hexRegionCls_topslant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean)
-/
@[path]
private lemma hexRegionCls_topslant_eq
  {R : HexRegion}
  {z : ℂ}
-- given
  (hz : Real.sqrt 3 * z.im = R.slant + z.re)
  (hne : z ≠ R.start)
  (hl : z.re ≠ 0)
  (hr : z.re ≠ R.width) :
-- imply
  hexRegionCls R z = 2 := by
-- proof
  apply StatMech.Universality.hexRegionCls_topslant R hz hne hl hr

/--
[hexRegionCls_botslant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean)
-/
@[path]
private lemma hexRegionCls_botslant_eq
  {R : HexRegion}
  {z : ℂ}
-- given
  (hz : Real.sqrt 3 * z.im = -(R.slant + z.re))
  (hne : z ≠ R.start)
  (hl : z.re ≠ 0)
  (hr : z.re ≠ R.width)
  (ht : Real.sqrt 3 * z.im ≠ R.slant + z.re) :
-- imply
  hexRegionCls R z = 3 := by
-- proof
  apply StatMech.Universality.hexRegionCls_botslant R hz hne hl hr ht

/--
[hexRegionCls_eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean)
-/
@[path]
private lemma hexRegionCls_eq_one_iff_eq
  {R : HexRegion}
  {z : ℂ} :
-- imply
  hexRegionCls R z = 1 ↔ z.re = 0 ∧ z ≠ R.start := by
-- proof
  apply StatMech.Universality.hexRegionCls_eq_one_iff R z

/--
[hexRegionCls_eq_four_imp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean)
-/
@[path]
private lemma hexRegionCls_eq_four_imp_eq
  {R : HexRegion}
  {z : ℂ}
-- given
  (h : hexRegionCls R z = 4) :
-- imply
  z.re = R.width := by
-- proof
  apply StatMech.Universality.hexRegionCls_eq_four_imp R z h

/--
[hexRegionCls_eq_two_imp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean)
-/
@[path]
private lemma hexRegionCls_eq_two_imp_eq
  {R : HexRegion}
  {z : ℂ}
-- given
  (h : hexRegionCls R z = 2) :
-- imply
  Real.sqrt 3 * z.im = R.slant + z.re := by
-- proof
  apply StatMech.Universality.hexRegionCls_eq_two_imp R z h

/--
[hexRegionCls_eq_three_imp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean)
-/
@[path]
private lemma hexRegionCls_eq_three_imp_eq
  {R : HexRegion}
  {z : ℂ}
-- given
  (h : hexRegionCls R z = 3) :
-- imply
  Real.sqrt 3 * z.im = -(R.slant + z.re) := by
-- proof
  apply StatMech.Universality.hexRegionCls_eq_three_imp R z h

/--
[hexRegionCls_start_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean)
-/
@[path]
private lemma hexRegionCls_start_eq_zero_eq
  {R : HexRegion} :
-- imply
  hexRegionCls R R.start = 0 := by
-- proof
  apply StatMech.Universality.hexRegionCls_start_eq_zero R

/--
[toFamilyData_lam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean)
-/
@[path]
private lemma toFamilyData_lam_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion} :
-- imply
  A.toFamilyData.lam = A.lam := by
-- proof
  apply StatMech.Universality.HexRegionAssign.toFamilyData_lam

/--
[toFamilyData_taup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean)
-/
@[path]
private lemma toFamilyData_taup_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion} :
-- imply
  A.toFamilyData.taup = A.taup := by
-- proof
  apply StatMech.Universality.HexRegionAssign.toFamilyData_taup

/--
[toFamilyData_taum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean)
-/
@[path]
private lemma toFamilyData_taum_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion} :
-- imply
  A.toFamilyData.taum = A.taum := by
-- proof
  apply StatMech.Universality.HexRegionAssign.toFamilyData_taum

/--
[toFamilyData_ups](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean)
-/
@[path]
private lemma toFamilyData_ups_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion} :
-- imply
  A.toFamilyData.ups = A.ups := by
-- proof
  apply StatMech.Universality.HexRegionAssign.toFamilyData_ups

/--
[toFamilyData_Fa](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean)
-/
@[path]
private lemma toFamilyData_Fa_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion} :
-- imply
  A.toFamilyData.Fa = A.Fa := by
-- proof
  apply StatMech.Universality.HexRegionAssign.toFamilyData_Fa

/--
[hexBdryAssign_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean)
-/
@[path]
private lemma hexBdryAssign_identity_eq
  [DecidableEq V]
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {R : HexRegion}
  {A : HexRegionAssign D P R}
-- given
  (hsub : P.interior ⊆ D.incidences)
  (hFa : A.Fa = 1) :
-- imply
  hexBdryCl * A.lam + hexBdryCt * (A.taup + A.taum) + A.ups = 1 := by
-- proof
  apply StatMech.Universality.hexBdryAssign_identity hsub A hFa

/--
[hexBdryAssign_identity_scales](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean)
-/
@[path]
private lemma hexBdryAssign_identity_scales_eq
  [DecidableEq V]
  {D : ℕ → HexDomain V}
  {P : ∀ v, (D v).InteriorPairing}
  {R : ℕ → HexRegion}
-- given
  (hsub : ∀ v, (P v).interior ⊆ (D v).incidences)
  (A : ∀ v, HexRegionAssign (D v) (P v) (R v))
  (hFa : ∀ v, 1 ≤ v → (A v).Fa = 1) :
-- imply
  ∀ v, 1 ≤ v → hexBdryCl * (A v).lam + hexBdryCt * ((A v).taup + (A v).taum) + (A v).ups = 1 := by
-- proof
  apply StatMech.Universality.hexBdryAssign_identity_scales hsub A hFa

/--
[hexCell_mid_zero_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean)
-/
@[path]
private lemma hexCell_mid_zero_re_eq
  [DecidableEq V]
  {c : ℂ} :
-- imply
  ((hexCell c).mid (0 : Fin 1) (0 : Fin 3)).re = Real.sqrt 3 / 4 := by
-- proof
  apply StatMech.Universality.hexCell_mid_zero_re c

/--
[hexCell_mid_two_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean)
-/
@[path]
private lemma hexCell_mid_two_re_eq
  [DecidableEq V]
  {c : ℂ} :
-- imply
  ((hexCell c).mid (0 : Fin 1) (2 : Fin 3)).re = 0 := by
-- proof
  apply StatMech.Universality.hexCell_mid_two_re c

/--
[hexRegionCls_hexCell_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean)
-/
@[path]
private lemma hexRegionCls_hexCell_two_eq
  [DecidableEq V]
  {c : ℂ}
  {R : HexRegion}
-- given
  (hne : (hexCell c).mid (0 : Fin 1) (2 : Fin 3) ≠ R.start) :
-- imply
  hexRegionCls R ((hexCell c).mid (0 : Fin 1) (2 : Fin 3)) = 1 := by
-- proof
  apply StatMech.Universality.hexRegionCls_hexCell_two c R hne


-- created on 2026-10-23

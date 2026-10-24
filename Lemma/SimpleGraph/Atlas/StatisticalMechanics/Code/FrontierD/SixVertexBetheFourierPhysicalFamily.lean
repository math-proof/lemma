import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalFamily
open StatMech StatMech.FrontierD


/--
[continuous_sixVertexAntiferroelectricLambda_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalFamily.lean)
-/
@[path]
private lemma continuous_sixVertexAntiferroelectricLambda_Icc_eq
  {a b : Real}
-- given
  (ha : 2 < a) :
-- imply
  Continuous (fun t : Set.Icc a b => sixVertexAntiferroelectricLambda t.1) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexAntiferroelectricLambda_Icc ha

/--
[sixVertexAntiferroelectricLambda_lower_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalFamily.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricLambda_lower_Icc_eq
  {a b : Real}
  {t : Set.Icc a b}
-- given
  (ha : 2 < a) :
-- imply
  sixVertexAntiferroelectricLambda a ≤ sixVertexAntiferroelectricLambda t.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricLambda_lower_Icc ha t

/--
[continuous_sixVertexXiFourier_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalFamily.lean)
-/
@[path]
private lemma continuous_sixVertexXiFourier_family_eq
  {a b : Real}
-- given
  (ha : 2 < a) :
-- imply
  Continuous (fun z : Set.Icc a b × Real => sixVertexXiFourier (sixVertexAntiferroelectricLambda z.1.1) z.2) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexXiFourier_family ha

/--
[continuous_sixVertexRapidityMomentum_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalFamily.lean)
-/
@[path]
private lemma continuous_sixVertexRapidityMomentum_family_eq
  {a b : Real}
-- given
  (ha : 2 < a) :
-- imply
  Continuous (fun z : Set.Icc a b × Set.Icc (-Real.pi) Real.pi => sixVertexRapidityMomentum (sixVertexAntiferroelectricLambda z.1.1) z.2.1) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexRapidityMomentum_family ha

/--
[continuous_sixVertexRapidityMomentumFamilyEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalFamily.lean)
-/
@[path]
private lemma continuous_sixVertexRapidityMomentumFamilyEquiv_eq
  {a b : Real}
-- given
  (ha : 2 < a) :
-- imply
  Continuous (sixVertexRapidityMomentumFamilyEquiv (b := b) ha) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexRapidityMomentumFamilyEquiv ha

/--
[continuous_sixVertexMomentumRapidityFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalFamily.lean)
-/
@[path]
private lemma continuous_sixVertexMomentumRapidityFamily_eq
  {a b : Real}
-- given
  (ha : 2 < a) :
-- imply
  Continuous (sixVertexMomentumRapidityFamily (b := b) ha : Set.Icc a b × Real → Real) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexMomentumRapidityFamily ha

/--
[sixVertexMomentumRapidityFamily_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalFamily.lean)
-/
@[path]
private lemma sixVertexMomentumRapidityFamily_eq_eq
  {a b : Real}
  {z : Set.Icc a b × Real}
-- given
  (ha : 2 < a) :
-- imply
  sixVertexMomentumRapidityFamily (b := b) ha z = sixVertexMomentumRapidity (sixVertexAntiferroelectricLambda z.1.1) (sixVertexAntiferroelectricLambda_pos (ha.trans_le z.1.2.1)) z.2 := by
-- proof
  apply StatMech.FrontierD.sixVertexMomentumRapidityFamily_eq ha z

/--
[continuous_sixVertexFourierRootDensity_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalFamily.lean)
-/
@[path]
private lemma continuous_sixVertexFourierRootDensity_family_eq
  {a b : Real}
-- given
  (ha : 2 < a) :
-- imply
  Continuous (fun z : Set.Icc a b × Real => sixVertexFourierRootDensity (sixVertexAntiferroelectricLambda z.1.1) z.2) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexFourierRootDensity_family ha

/--
[continuous_sixVertexRootDensityWeight_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalFamily.lean)
-/
@[path]
private lemma continuous_sixVertexRootDensityWeight_family_eq
  {a b : Real}
-- given
  (ha : 2 < a) :
-- imply
  Continuous (fun z : Set.Icc a b × Real => sixVertexRootDensityWeight z.1.1 z.2) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexRootDensityWeight_family ha

/--
[continuous_sixVertexFourierPhysicalDensityFamily_fun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalFamily.lean)
-/
@[path]
private lemma continuous_sixVertexFourierPhysicalDensityFamily_fun_eq
  {a b : Real}
-- given
  (ha : 2 < a) :
-- imply
  Continuous (fun z : Set.Icc a b × Real => sixVertexFourierRootDensity (sixVertexAntiferroelectricLambda z.1.1) (sixVertexMomentumRapidityFamily (b := b) ha z) / (2 * Real.pi * sixVertexRootDensityWeight z.1.1 z.2)) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexFourierPhysicalDensityFamily_fun ha

/--
[sixVertexFourierPhysicalDensityFamily_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalFamily.lean)
-/
@[path]
private lemma sixVertexFourierPhysicalDensityFamily_apply_eq
  {a b : Real}
  {z : Set.Icc a b × Real}
-- given
  (ha : 2 < a) :
-- imply
  sixVertexFourierPhysicalDensityFamily ha z = sixVertexFourierPhysicalDensity z.1.1 (ha.trans_le z.1.2.1) z.2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourierPhysicalDensityFamily_apply ha z

/--
[sixVertexFourierPhysicalDensityFamily_continuumEquation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalFamily.lean)
-/
@[path]
private lemma sixVertexFourierPhysicalDensityFamily_continuumEquation_eq
  {a b : Real}
  {t : Set.Icc a b}
-- given
  (ha : 2 < a) :
-- imply
  SixVertexSatisfiesContinuousDensityEquation t.1 (sixVertexContinuumDensityAt (sixVertexFourierPhysicalDensityFamily ha) t) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourierPhysicalDensityFamily_continuumEquation ha t

/--
[intervalIntegral_sixVertexFourierPhysicalDensityFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalFamily.lean)
-/
@[path]
private lemma intervalIntegral_sixVertexFourierPhysicalDensityFamily_eq
  {a b : Real}
  {t : Set.Icc a b}
-- given
  (ha : 2 < a) :
-- imply
  (∫ x in -Real.pi..Real.pi, sixVertexContinuumDensityAt (sixVertexFourierPhysicalDensityFamily ha) t x) = 1 / 2 := by
-- proof
  apply StatMech.FrontierD.intervalIntegral_sixVertexFourierPhysicalDensityFamily ha t


-- created on 2026-10-23

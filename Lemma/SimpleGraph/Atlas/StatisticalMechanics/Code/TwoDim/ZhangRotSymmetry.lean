import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangRotSymmetry.Part3
open MeasureTheory Set Filter Topology StatMech StatMech.TwoDim


/--
[zrs_rotConfig_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangRotSymmetry.lean)
-/
@[path]
private lemma zrs_rotConfig_apply_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  kdi_rotConfig ω e = ω (kdi_rotEdgeEquiv.symm e) := by
-- proof
  apply StatMech.TwoDim.zrs_rotConfig_apply ω e

/--
[zrs_rotConfig_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangRotSymmetry.lean)
-/
@[path]
private lemma zrs_rotConfig_monotone_eq :
-- imply
  Monotone (kdi_rotConfig) := by
-- proof
  apply StatMech.TwoDim.zrs_rotConfig_monotone

/--
[zrs_rotPreimage_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangRotSymmetry.lean)
-/
@[path]
private lemma zrs_rotPreimage_isIncreasing_eq
  {A : Set (ConfigSpace (Sym2 (Site 2)))}
-- given
  (hA : IsIncreasing A) :
-- imply
  IsIncreasing (kdi_rotConfig ⁻¹' A) := by
-- proof
  apply StatMech.TwoDim.zrs_rotPreimage_isIncreasing hA

/--
[zrs_rotPreimage_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangRotSymmetry.lean)
-/
@[path]
private lemma zrs_rotPreimage_measurableSet_eq
  {A : Set (ConfigSpace (Sym2 (Site 2)))}
-- given
  (hA : MeasurableSet A) :
-- imply
  MeasurableSet (kdi_rotConfig ⁻¹' A) := by
-- proof
  apply StatMech.TwoDim.zrs_rotPreimage_measurableSet hA

/--
[zrs_rotPreimage_measureReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangRotSymmetry.lean)
-/
@[path]
private lemma zrs_rotPreimage_measureReal_eq
  {A : Set (ConfigSpace (Sym2 (Site 2)))}
-- given
  (hA : MeasurableSet A) :
-- imply
  halfMeasure.real (kdi_rotConfig ⁻¹' A) = halfMeasure.real A := by
-- proof
  apply StatMech.TwoDim.zrs_rotPreimage_measureReal hA

/--
[zrs_sideFamily_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangRotSymmetry.lean)
-/
@[path]
private lemma zrs_sideFamily_zero_eq
  {base : Set (ConfigSpace (Sym2 (Site 2)))} :
-- imply
  zrs_sideFamily base 0 = base := by
-- proof
  apply StatMech.TwoDim.zrs_sideFamily_zero base

/--
[zrs_sideFamily_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangRotSymmetry.lean)
-/
@[path]
private lemma zrs_sideFamily_one_eq
  {base : Set (ConfigSpace (Sym2 (Site 2)))} :
-- imply
  zrs_sideFamily base 1 = zrs_rot (zrs_rot base) := by
-- proof
  apply StatMech.TwoDim.zrs_sideFamily_one base

/--
[zrs_sideFamily_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangRotSymmetry.lean)
-/
@[path]
private lemma zrs_sideFamily_two_eq
  {base : Set (ConfigSpace (Sym2 (Site 2)))} :
-- imply
  zrs_sideFamily base 2 = zrs_rot base := by
-- proof
  apply StatMech.TwoDim.zrs_sideFamily_two base

/--
[zrs_sideFamily_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangRotSymmetry.lean)
-/
@[path]
private lemma zrs_sideFamily_three_eq
  {base : Set (ConfigSpace (Sym2 (Site 2)))} :
-- imply
  zrs_sideFamily base 3 = zrs_rot (zrs_rot (zrs_rot base)) := by
-- proof
  apply StatMech.TwoDim.zrs_sideFamily_three base

/--
[zrs_sideFamily_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangRotSymmetry.lean)
-/
@[path]
private lemma zrs_sideFamily_isIncreasing_eq
  {base : Set (ConfigSpace (Sym2 (Site 2)))}
  {i : Fin 4}
-- given
  (hbase : IsIncreasing base) :
-- imply
  IsIncreasing (zrs_sideFamily base i) := by
-- proof
  apply StatMech.TwoDim.zrs_sideFamily_isIncreasing hbase i

/--
[zrs_sideFamily_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangRotSymmetry.lean)
-/
@[path]
private lemma zrs_sideFamily_measurableSet_eq
  {base : Set (ConfigSpace (Sym2 (Site 2)))}
  {i : Fin 4}
-- given
  (hbase : MeasurableSet base) :
-- imply
  MeasurableSet (zrs_sideFamily base i) := by
-- proof
  apply StatMech.TwoDim.zrs_sideFamily_measurableSet hbase i

/--
[zrs_side_symmetry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangRotSymmetry.lean)
-/
@[path]
private lemma zrs_side_symmetry_eq
  {base : Set (ConfigSpace (Sym2 (Site 2)))}
  {i : Fin 4}
-- given
  (hbase : MeasurableSet base) :
-- imply
  halfMeasure.real (zrs_sideFamily base i) = halfMeasure.real (zrs_sideFamily base 0) := by
-- proof
  apply StatMech.TwoDim.zrs_side_symmetry hbase i

/--
[zrs_geometricData_Ssym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangRotSymmetry.lean)
-/
@[path]
private lemma zrs_geometricData_Ssym_eq
  {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
  {base : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
  {Err : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
-- given
  (hbaseInc : ∀ n, IsIncreasing (base n))
  (hbaseM : ∀ n, MeasurableSet (base n))
  (herr : Tendsto (fun n => halfMeasure.real (Err n)) atTop (𝓝 0))
  (hunion : Tendsto (fun n => halfMeasure.real (zrs_sideFamily (base n) 0 ∪ zrs_sideFamily (base n) 1 ∪ zrs_sideFamily (base n) 2 ∪ zrs_sideFamily (base n) 3)) atTop (𝓝 1))
  (hmerge : ∀ n, zrs_sideFamily (base n) 0 ∩ zrs_sideFamily (base n) 1 ⊆ (A n ∪ B n) ∪ Err n) :
-- imply
  ∀ i n, halfMeasure.real ((zrs_geometricData_of_remaining base Err hbaseInc hbaseM herr hunion hmerge).S i n) = halfMeasure.real ((zrs_geometricData_of_remaining base Err hbaseInc hbaseM herr hunion hmerge).S 0 n) := by
-- proof
  apply StatMech.TwoDim.zrs_geometricData_Ssym base Err hbaseInc hbaseM herr hunion hmerge

/--
[zrs_zhangUnion_of_remaining](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangRotSymmetry.lean)
-/
@[path]
private lemma zrs_zhangUnion_of_remaining_eq
  {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
  {base : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
  {Err : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
-- given
  (hpa : PositivelyAssociated halfMeasure)
  (hbaseInc : ∀ n, IsIncreasing (base n))
  (hbaseM : ∀ n, MeasurableSet (base n))
  (herr : Tendsto (fun n => halfMeasure.real (Err n)) atTop (𝓝 0))
  (hunion : Tendsto (fun n => halfMeasure.real (zrs_sideFamily (base n) 0 ∪ zrs_sideFamily (base n) 1 ∪ zrs_sideFamily (base n) 2 ∪ zrs_sideFamily (base n) 3)) atTop (𝓝 1))
  (hmerge : ∀ n, zrs_sideFamily (base n) 0 ∩ zrs_sideFamily (base n) 1 ⊆ (A n ∪ B n) ∪ Err n) :
-- imply
  Tendsto (fun n => halfMeasure.real (A n ∪ B n)) atTop (𝓝 1) := by
-- proof
  apply StatMech.TwoDim.zrs_zhangUnion_of_remaining hpa base Err hbaseInc hbaseM herr hunion hmerge


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization.Part4
open Finset StatMech StatMech.FrontierD


/--
[sixVertexHorizontalPairBoundedFineRowProfile_eq_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineFiberFactorization.lean)
-/
@[path]
private lemma sixVertexHorizontalPairBoundedFineRowProfile_eq_add_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairBoundedFineRowProfile horizontal = sixVertexHorizontalAddSingleRowProfiles (sixVertexHorizontalBoundedSingleRowProfile horizontal.1) (sixVertexHorizontalBoundedSingleRowProfile horizontal.2) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalPairBoundedFineRowProfile_eq_add horizontal

/--
[sixVertexHorizontalPairBigrade_eq_fineRowProfileGrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineFiberFactorization.lean)
-/
@[path]
private lemma sixVertexHorizontalPairBigrade_eq_fineRowProfileGrade_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairBigrade horizontal = sixVertexHorizontalFineRowProfileGrade (sixVertexHorizontalPairBoundedFineRowProfile horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalPairBigrade_eq_fineRowProfileGrade horizontal

/--
[sixVertexHorizontalPairRowZeroProfile_eq_fineRowProfileRowZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineFiberFactorization.lean)
-/
@[path]
private lemma sixVertexHorizontalPairRowZeroProfile_eq_fineRowProfileRowZero_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairRowZeroProfile horizontal = sixVertexHorizontalFineRowProfileRowZero (sixVertexHorizontalPairBoundedFineRowProfile horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalPairRowZeroProfile_eq_fineRowProfileRowZero horizontal

/--
[sixVertexHorizontalFineRowProfileSectorPairSum_eq_convolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineFiberFactorization.lean)
-/
@[path]
private lemma sixVertexHorizontalFineRowProfileSectorPairSum_eq_convolution_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T} :
-- imply
  sixVertexHorizontalFineRowProfileSectorPairSum T left right profile = ∑ first : SixVertexHorizontalBoundedSingleRowProfile T, ∑ second : SixVertexHorizontalBoundedSingleRowProfile T, if sixVertexHorizontalAddSingleRowProfiles first second = profile then sixVertexHorizontalSingleRowProfileSectorSum T left first * sixVertexHorizontalSingleRowProfileSectorSum T right second else 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalFineRowProfileSectorPairSum_eq_convolution T left right profile

/--
[sixVertexHorizontalFineRowProfileSignedSum_eq_minorConvolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineFiberFactorization.lean)
-/
@[path]
private lemma sixVertexHorizontalFineRowProfileSignedSum_eq_minorConvolution_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T} :
-- imply
  sixVertexHorizontalFineRowProfileSignedSum T sourceLeft sourceRight targetLeft targetRight profile = ∑ first : SixVertexHorizontalBoundedSingleRowProfile T, ∑ second : SixVertexHorizontalBoundedSingleRowProfile T, if sixVertexHorizontalAddSingleRowProfiles first second = profile then (sixVertexHorizontalSingleRowProfileSectorSum T targetLeft first : Int) * sixVertexHorizontalSingleRowProfileSectorSum T targetRight second - (sixVertexHorizontalSingleRowProfileSectorSum T sourceLeft first : Int) * sixVertexHorizontalSingleRowProfileSectorSum T sourceRight second else 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalFineRowProfileSignedSum_eq_minorConvolution T sourceLeft sourceRight targetLeft targetRight profile

/--
[sixVertexHorizontalFineRowProfileSignedSum_eq_kernelSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineFiberFactorization.lean)
-/
@[path]
private lemma sixVertexHorizontalFineRowProfileSignedSum_eq_kernelSum_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T} :
-- imply
  sixVertexHorizontalFineRowProfileSignedSum T sourceLeft sourceRight targetLeft targetRight profile = ∑ horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T, if sixVertexHorizontalPairBoundedFineRowProfile horizontal = profile then sixVertexHorizontalProfileSignedKernel sourceLeft sourceRight targetLeft targetRight (sixVertexHorizontalPairCompletionProfile T horizontal) else 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalFineRowProfileSignedSum_eq_kernelSum T sourceLeft sourceRight targetLeft targetRight profile

/--
[fineRowProfileSignedNonnegative_of_raw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineFiberFactorization.lean)
-/
@[path]
private lemma fineRowProfileSignedNonnegative_of_raw_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
-- given
  (hraw : forall profile : SixVertexHorizontalBoundedFineRowProfile T, 0 <= sixVertexHorizontalFineRowProfileSignedSum T sourceLeft sourceRight targetLeft targetRight profile) :
-- imply
  SixVertexHorizontalFineRowProfileAggregateSignedNonnegative T sourceLeft sourceRight targetLeft targetRight := by
-- proof
  apply StatMech.FrontierD.fineRowProfileSignedNonnegative_of_raw T sourceLeft sourceRight targetLeft targetRight hraw

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_rawFineProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineFiberFactorization.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_rawFineProfile_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hraw : forall profile : SixVertexHorizontalBoundedFineRowProfile T, 0 <= sixVertexHorizontalFineRowProfileSignedSum T ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩ middle middle profile) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_rawFineProfile T middle hmiddle_pos hmiddle_lt hraw


-- created on 2026-10-23

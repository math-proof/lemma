import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds
open StatMech StatMech.Exact3D StatMech.Exact3D.FinitePlusTailBlockBounds


/--
[map_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma map_finite_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {x : FinitePlusTailState n α} :
-- imply
  (B.map x).finite = B.finiteMap x := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.map_finite B x

/--
[map_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma map_tail_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {x : FinitePlusTailState n α} :
-- imply
  (B.map x).tail = B.tailMap x := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.map_tail B x

/--
[map_finite_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma map_finite_bound_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {x y : FinitePlusTailState n α} :
-- imply
  (B.map x).finiteDist (B.map y) ≤ B.finiteToFinite * x.finiteDist y + B.tailToFinite * x.tailDist y := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.map_finite_bound B x y

/--
[map_tail_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma map_tail_bound_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {x y : FinitePlusTailState n α} :
-- imply
  (B.map x).tailDist (B.map y) ≤ B.finiteToTail * x.finiteDist y + B.tailToTail * x.tailDist y := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.map_tail_bound B x y

/--
[with_larger_constants_finiteMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma with_larger_constants_finiteMap_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
-- given
  (hff : B.finiteToFinite ≤ finiteToFinite')
  (htf : B.tailToFinite ≤ tailToFinite')
  (hft : B.finiteToTail ≤ finiteToTail')
  (htt : B.tailToTail ≤ tailToTail') :
-- imply
  (B.with_larger_constants hff htf hft htt).finiteMap = B.finiteMap := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.with_larger_constants_finiteMap B hff htf hft htt

/--
[with_larger_constants_tailMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma with_larger_constants_tailMap_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
-- given
  (hff : B.finiteToFinite ≤ finiteToFinite')
  (htf : B.tailToFinite ≤ tailToFinite')
  (hft : B.finiteToTail ≤ finiteToTail')
  (htt : B.tailToTail ≤ tailToTail') :
-- imply
  (B.with_larger_constants hff htf hft htt).tailMap = B.tailMap := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.with_larger_constants_tailMap B hff htf hft htt

/--
[with_larger_constants_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma with_larger_constants_map_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
-- given
  (hff : B.finiteToFinite ≤ finiteToFinite')
  (htf : B.tailToFinite ≤ tailToFinite')
  (hft : B.finiteToTail ≤ finiteToTail')
  (htt : B.tailToTail ≤ tailToTail') :
-- imply
  (B.with_larger_constants hff htf hft htt).map = B.map := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.with_larger_constants_map B hff htf hft htt

/--
[with_larger_constants_finiteToFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma with_larger_constants_finiteToFinite_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
-- given
  (hff : B.finiteToFinite ≤ finiteToFinite')
  (htf : B.tailToFinite ≤ tailToFinite')
  (hft : B.finiteToTail ≤ finiteToTail')
  (htt : B.tailToTail ≤ tailToTail') :
-- imply
  (B.with_larger_constants hff htf hft htt).finiteToFinite = finiteToFinite' := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.with_larger_constants_finiteToFinite B hff htf hft htt

/--
[with_larger_constants_tailToFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma with_larger_constants_tailToFinite_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
-- given
  (hff : B.finiteToFinite ≤ finiteToFinite')
  (htf : B.tailToFinite ≤ tailToFinite')
  (hft : B.finiteToTail ≤ finiteToTail')
  (htt : B.tailToTail ≤ tailToTail') :
-- imply
  (B.with_larger_constants hff htf hft htt).tailToFinite = tailToFinite' := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.with_larger_constants_tailToFinite B hff htf hft htt

/--
[with_larger_constants_finiteToTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma with_larger_constants_finiteToTail_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
-- given
  (hff : B.finiteToFinite ≤ finiteToFinite')
  (htf : B.tailToFinite ≤ tailToFinite')
  (hft : B.finiteToTail ≤ finiteToTail')
  (htt : B.tailToTail ≤ tailToTail') :
-- imply
  (B.with_larger_constants hff htf hft htt).finiteToTail = finiteToTail' := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.with_larger_constants_finiteToTail B hff htf hft htt

/--
[with_larger_constants_tailToTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma with_larger_constants_tailToTail_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
-- given
  (hff : B.finiteToFinite ≤ finiteToFinite')
  (htf : B.tailToFinite ≤ tailToFinite')
  (hft : B.finiteToTail ≤ finiteToTail')
  (htt : B.tailToTail ≤ tailToTail') :
-- imply
  (B.with_larger_constants hff htf hft htt).tailToTail = tailToTail' := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.with_larger_constants_tailToTail B hff htf hft htt

/--
[toLipschitzCertificate_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toLipschitzCertificate_map_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c) :
-- imply
  (B.toLipschitzCertificate hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le).map = B.map := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toLipschitzCertificate_map B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le

/--
[toLipschitzCertificate_c](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toLipschitzCertificate_c_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c) :
-- imply
  (B.toLipschitzCertificate hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le).c = c := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toLipschitzCertificate_c B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le

/--
[mixed_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma mixed_lipschitz_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {x y : FinitePlusTailState n α}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c) :
-- imply
  (B.map x).dist (B.map y) ≤ c * x.dist y := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.mixed_lipschitz B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le x y

/--
[exists_unique_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma exists_unique_fixedPoint_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c) :
-- imply
  ∃! p : FinitePlusTailState n α, B.map p = p := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.exists_unique_fixedPoint B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le

/--
[toClosedBallCertificate_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificate_contraction_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius residual : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hresidual : (B.map center).dist center ≤ residual)
  (hbudget : residual + c * radius ≤ radius) :
-- imply
  (B.toClosedBallCertificate hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hresidual hbudget).contraction = B.toLipschitzCertificate hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificate_contraction B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hresidual hbudget

/--
[toClosedBallCertificate_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificate_center_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius residual : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hresidual : (B.map center).dist center ≤ residual)
  (hbudget : residual + c * radius ≤ radius) :
-- imply
  (B.toClosedBallCertificate hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hresidual hbudget).center = center := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificate_center B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hresidual hbudget

/--
[toClosedBallCertificate_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificate_radius_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius residual : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hresidual : (B.map center).dist center ≤ residual)
  (hbudget : residual + c * radius ≤ radius) :
-- imply
  (B.toClosedBallCertificate hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hresidual hbudget).radius = radius := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificate_radius B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hresidual hbudget

/--
[toClosedBallCertificate_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificate_residual_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius residual : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hresidual : (B.map center).dist center ≤ residual)
  (hbudget : residual + c * radius ≤ radius) :
-- imply
  (B.toClosedBallCertificate hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hresidual hbudget).residual = residual := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificate_residual B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hresidual hbudget

/--
[toClosedBallCertificate_fixedPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificate_fixedPoint_mem_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius residual : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hresidual : (B.map center).dist center ≤ residual)
  (hbudget : residual + c * radius ≤ radius) :
-- imply
  FinitePlusTailState.ClosedBall center radius (B.toClosedBallCertificate hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hresidual hbudget).fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificate_fixedPoint_mem B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hresidual hbudget

/--
[toClosedBallCertificate_fixedPoint_isFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificate_fixedPoint_isFixed_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius residual : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hresidual : (B.map center).dist center ≤ residual)
  (hbudget : residual + c * radius ≤ radius) :
-- imply
  B.map (B.toClosedBallCertificate hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hresidual hbudget).fixedPoint = (B.toClosedBallCertificate hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hresidual hbudget).fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificate_fixedPoint_isFixed B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hresidual hbudget

/--
[toClosedBallCertificate_exists_unique_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificate_exists_unique_fixedPoint_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius residual : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hresidual : (B.map center).dist center ≤ residual)
  (hbudget : residual + c * radius ≤ radius) :
-- imply
  ∃! p : FinitePlusTailState n α, (B.toClosedBallCertificate hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hresidual hbudget).contraction.map p = p := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificate_exists_unique_fixedPoint B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hresidual hbudget

/--
[toClosedBallCertificate_mapsClosedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificate_mapsClosedBall_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius residual : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hresidual : (B.map center).dist center ≤ residual)
  (hbudget : residual + c * radius ≤ radius) :
-- imply
  FinitePlusTailState.MapsClosedBall B.map center radius := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificate_mapsClosedBall B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hresidual hbudget

/--
[residual_bound_of_componentResiduals](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma residual_bound_of_componentResiduals_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {center : FinitePlusTailState n α}
  {finiteResidual tailResidual : ℝ}
-- given
  (hfinite : FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤ finiteResidual)
  (htail : (B.tailMap center).dist center.tail ≤ tailResidual) :
-- imply
  (B.map center).dist center ≤ finiteResidual + tailResidual := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.residual_bound_of_componentResiduals B center hfinite htail

/--
[finiteResidual_le_of_vectorMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma finiteResidual_le_of_vectorMem_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {center : FinitePlusTailState n α}
  {R : RatInterval.IntervalVector n}
-- given
  (hR : RatInterval.VectorMem (fun i => B.finiteMap center i - center.finite i) R) :
-- imply
  FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤ (RatInterval.VectorAbsSum R : ℝ) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.finiteResidual_le_of_vectorMem B center hR

/--
[toClosedBallCertificateOfComponentResiduals_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificateOfComponentResiduals_contraction_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius finiteResidual tailResidual : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hfinite : FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤ finiteResidual)
  (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
  (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
-- imply
  (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfinite htail hbudget).contraction = B.toLipschitzCertificate hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificateOfComponentResiduals_contraction B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfinite htail hbudget

/--
[toClosedBallCertificateOfComponentResiduals_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificateOfComponentResiduals_center_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius finiteResidual tailResidual : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hfinite : FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤ finiteResidual)
  (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
  (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
-- imply
  (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfinite htail hbudget).center = center := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificateOfComponentResiduals_center B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfinite htail hbudget

/--
[toClosedBallCertificateOfComponentResiduals_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificateOfComponentResiduals_radius_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius finiteResidual tailResidual : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hfinite : FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤ finiteResidual)
  (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
  (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
-- imply
  (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfinite htail hbudget).radius = radius := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificateOfComponentResiduals_radius B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfinite htail hbudget

/--
[toClosedBallCertificateOfComponentResiduals_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificateOfComponentResiduals_residual_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius finiteResidual tailResidual : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hfinite : FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤ finiteResidual)
  (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
  (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
-- imply
  (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfinite htail hbudget).residual = finiteResidual + tailResidual := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificateOfComponentResiduals_residual B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfinite htail hbudget

/--
[toClosedBallCertificateOfComponentResiduals_fixedPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificateOfComponentResiduals_fixedPoint_mem_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius finiteResidual tailResidual : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hfinite : FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤ finiteResidual)
  (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
  (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
-- imply
  FinitePlusTailState.ClosedBall center radius (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfinite htail hbudget).fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificateOfComponentResiduals_fixedPoint_mem B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfinite htail hbudget

/--
[toClosedBallCertificateOfComponentResiduals_fixedPoint_isFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificateOfComponentResiduals_fixedPoint_isFixed_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius finiteResidual tailResidual : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hfinite : FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤ finiteResidual)
  (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
  (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
-- imply
  B.map (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfinite htail hbudget).fixedPoint = (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfinite htail hbudget).fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificateOfComponentResiduals_fixedPoint_isFixed B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfinite htail hbudget

/--
[toClosedBallCertificateOfComponentResiduals_exists_unique_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificateOfComponentResiduals_exists_unique_fixedPoint_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius finiteResidual tailResidual : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hfinite : FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤ finiteResidual)
  (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
  (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
-- imply
  ∃! p : FinitePlusTailState n α, (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfinite htail hbudget).contraction.map p = p := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificateOfComponentResiduals_exists_unique_fixedPoint B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfinite htail hbudget

/--
[toClosedBallCertificateOfComponentResiduals_mapsClosedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificateOfComponentResiduals_mapsClosedBall_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius finiteResidual tailResidual : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hfinite : FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤ finiteResidual)
  (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
  (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
-- imply
  FinitePlusTailState.MapsClosedBall B.map center radius := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificateOfComponentResiduals_mapsClosedBall B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfinite htail hbudget

/--
[toClosedBallCertificateOfFiniteResidualVector_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificateOfFiniteResidualVector_contraction_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius tailResidual : ℝ}
  {R : RatInterval.IntervalVector n}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hfiniteResidualMem : RatInterval.VectorMem (fun i => B.finiteMap center i - center.finite i) R)
  (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
  (hbudget : (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤ radius) :
-- imply
  (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfiniteResidualMem htail hbudget).contraction = B.toLipschitzCertificate hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificateOfFiniteResidualVector_contraction B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfiniteResidualMem htail hbudget

/--
[toClosedBallCertificateOfFiniteResidualVector_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificateOfFiniteResidualVector_center_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius tailResidual : ℝ}
  {R : RatInterval.IntervalVector n}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hfiniteResidualMem : RatInterval.VectorMem (fun i => B.finiteMap center i - center.finite i) R)
  (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
  (hbudget : (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤ radius) :
-- imply
  (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfiniteResidualMem htail hbudget).center = center := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificateOfFiniteResidualVector_center B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfiniteResidualMem htail hbudget

/--
[toClosedBallCertificateOfFiniteResidualVector_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificateOfFiniteResidualVector_radius_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius tailResidual : ℝ}
  {R : RatInterval.IntervalVector n}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hfiniteResidualMem : RatInterval.VectorMem (fun i => B.finiteMap center i - center.finite i) R)
  (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
  (hbudget : (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤ radius) :
-- imply
  (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfiniteResidualMem htail hbudget).radius = radius := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificateOfFiniteResidualVector_radius B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfiniteResidualMem htail hbudget

/--
[toClosedBallCertificateOfFiniteResidualVector_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificateOfFiniteResidualVector_residual_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius tailResidual : ℝ}
  {R : RatInterval.IntervalVector n}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hfiniteResidualMem : RatInterval.VectorMem (fun i => B.finiteMap center i - center.finite i) R)
  (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
  (hbudget : (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤ radius) :
-- imply
  (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfiniteResidualMem htail hbudget).residual = (RatInterval.VectorAbsSum R : ℝ) + tailResidual := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificateOfFiniteResidualVector_residual B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfiniteResidualMem htail hbudget

/--
[toClosedBallCertificateOfFiniteResidualVector_fixedPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificateOfFiniteResidualVector_fixedPoint_mem_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius tailResidual : ℝ}
  {R : RatInterval.IntervalVector n}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hfiniteResidualMem : RatInterval.VectorMem (fun i => B.finiteMap center i - center.finite i) R)
  (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
  (hbudget : (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤ radius) :
-- imply
  FinitePlusTailState.ClosedBall center radius (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfiniteResidualMem htail hbudget).fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificateOfFiniteResidualVector_fixedPoint_mem B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfiniteResidualMem htail hbudget

/--
[toClosedBallCertificateOfFiniteResidualVector_fixedPoint_isFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificateOfFiniteResidualVector_fixedPoint_isFixed_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius tailResidual : ℝ}
  {R : RatInterval.IntervalVector n}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hfiniteResidualMem : RatInterval.VectorMem (fun i => B.finiteMap center i - center.finite i) R)
  (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
  (hbudget : (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤ radius) :
-- imply
  B.map (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfiniteResidualMem htail hbudget).fixedPoint = (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfiniteResidualMem htail hbudget).fixedPoint := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificateOfFiniteResidualVector_fixedPoint_isFixed B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfiniteResidualMem htail hbudget

/--
[toClosedBallCertificateOfFiniteResidualVector_exists_unique_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificateOfFiniteResidualVector_exists_unique_fixedPoint_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius tailResidual : ℝ}
  {R : RatInterval.IntervalVector n}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hfiniteResidualMem : RatInterval.VectorMem (fun i => B.finiteMap center i - center.finite i) R)
  (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
  (hbudget : (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤ radius) :
-- imply
  ∃! p : FinitePlusTailState n α, (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfiniteResidualMem htail hbudget).contraction.map p = p := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificateOfFiniteResidualVector_exists_unique_fixedPoint B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfiniteResidualMem htail hbudget

/--
[toClosedBallCertificateOfFiniteResidualVector_mapsClosedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean)
-/
@[path]
private lemma toClosedBallCertificateOfFiniteResidualVector_mapsClosedBall_eq
  {n : ℕ}
  {B : FinitePlusTailBlockBounds n α}
  {c : ℝ}
  {center : FinitePlusTailState n α}
  {radius tailResidual : ℝ}
  {R : RatInterval.IntervalVector n}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
  (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
  (hradius : 0 ≤ radius)
  (hfiniteResidualMem : RatInterval.VectorMem (fun i => B.finiteMap center i - center.finite i) R)
  (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
  (hbudget : (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤ radius) :
-- imply
  FinitePlusTailState.MapsClosedBall B.map center radius := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockBounds.toClosedBallCertificateOfFiniteResidualVector_mapsClosedBall B hc_nonneg hc_lt_one hfinite_column_sum_le htail_column_sum_le center hradius hfiniteResidualMem htail hbudget


-- created on 2026-10-23

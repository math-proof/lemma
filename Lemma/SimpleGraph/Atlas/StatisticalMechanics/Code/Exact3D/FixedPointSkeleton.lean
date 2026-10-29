import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
open StatMech StatMech.Exact3D StatMech.Exact3D.FiniteContraction StatMech.Exact3D.FiniteContraction.L1Vector StatMech.Exact3D.FiniteContraction.ClosedBallContractionCertificate StatMech.Exact3D.FiniteContraction.NonzeroAffineExample StatMech.Exact3D.FiniteContraction.ZeroLinearExample


/--
[l1Dist_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma l1Dist_nonneg_eq
  {n : ℕ}
  {x y : Fin n → ℝ} :
-- imply
  0 ≤ l1Dist x y := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.l1Dist_nonneg x y

/--
[abs_sub_coord_le_l1Dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma abs_sub_coord_le_l1Dist_eq
  {n : ℕ}
  {x y : Fin n → ℝ}
  {i : Fin n} :
-- imply
  |x i - y i| ≤ l1Dist x y := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.abs_sub_coord_le_l1Dist x y i

/--
[eq_of_l1Dist_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma eq_of_l1Dist_eq_zero_eq
  {n : ℕ}
  {x y : Fin n → ℝ}
-- given
  (h : l1Dist x y = 0) :
-- imply
  x = y := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.eq_of_l1Dist_eq_zero h

/--
[lipschitzWithConstant_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma lipschitzWithConstant_mono_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {c c' : ℝ}
-- given
  (hLip : LipschitzWithConstant F c)
  (hc : c ≤ c') :
-- imply
  LipschitzWithConstant F c' := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.lipschitzWithConstant_mono hLip hc

/--
[matVec_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma matVec_sub_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {x y : Fin n → ℝ}
  {i : Fin n} :
-- imply
  RatInterval.matVec A x i - RatInterval.matVec A y i = RatInterval.matVec A (fun j => x j - y j) i := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.matVec_sub A x y i

/--
[affineMap_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma affineMap_sub_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {b : Fin n → ℝ}
  {x y : Fin n → ℝ}
  {i : Fin n} :
-- imply
  RatInterval.affineMap A b x i - RatInterval.affineMap A b y i = RatInterval.matVec A (fun j => x j - y j) i := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.affineMap_sub A b x y i

/--
[lipschitz_matVec_of_rowSumContraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma lipschitz_matVec_of_rowSumContraction_eq
  {n : ℕ}
  {I : RatInterval.IntervalMatrix n n}
  {A : Fin n → Fin n → ℝ}
-- given
  (hI : RatInterval.RowSumContraction I)
  (hA : RatInterval.MatrixMem A I) :
-- imply
  LipschitzWithConstant (fun x i => RatInterval.matVec A x i) ((n : ℝ) * (hI.c : ℝ)) := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.lipschitz_matVec_of_rowSumContraction hI hA

/--
[lipschitz_matVec_of_columnSumContraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma lipschitz_matVec_of_columnSumContraction_eq
  {n : ℕ}
  {I : RatInterval.IntervalMatrix n n}
  {A : Fin n → Fin n → ℝ}
-- given
  (hI : RatInterval.ColumnSumContraction I)
  (hA : RatInterval.MatrixMem A I) :
-- imply
  LipschitzWithConstant (fun x i => RatInterval.matVec A x i) (hI.c : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.lipschitz_matVec_of_columnSumContraction hI hA

/--
[lipschitz_affineMap_of_rowSumContraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma lipschitz_affineMap_of_rowSumContraction_eq
  {n : ℕ}
  {I : RatInterval.IntervalMatrix n n}
  {A : Fin n → Fin n → ℝ}
  {b : Fin n → ℝ}
-- given
  (hI : RatInterval.RowSumContraction I)
  (hA : RatInterval.MatrixMem A I) :
-- imply
  LipschitzWithConstant (fun x i => RatInterval.affineMap A b x i) ((n : ℝ) * (hI.c : ℝ)) := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.lipschitz_affineMap_of_rowSumContraction hI hA b

/--
[lipschitz_affineMap_of_columnSumContraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma lipschitz_affineMap_of_columnSumContraction_eq
  {n : ℕ}
  {I : RatInterval.IntervalMatrix n n}
  {A : Fin n → Fin n → ℝ}
  {b : Fin n → ℝ}
-- given
  (hI : RatInterval.ColumnSumContraction I)
  (hA : RatInterval.MatrixMem A I) :
-- imply
  LipschitzWithConstant (fun x i => RatInterval.affineMap A b x i) (hI.c : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.lipschitz_affineMap_of_columnSumContraction hI hA b

/--
[lipschitz_affineMatVec_of_rowSumContraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma lipschitz_affineMatVec_of_rowSumContraction_eq
  {n : ℕ}
  {I : RatInterval.IntervalMatrix n n}
  {A : Fin n → Fin n → ℝ}
  {b : Fin n → ℝ}
-- given
  (hI : RatInterval.RowSumContraction I)
  (hA : RatInterval.MatrixMem A I) :
-- imply
  LipschitzWithConstant (fun x i => RatInterval.matVec A x i + b i) ((n : ℝ) * (hI.c : ℝ)) := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.lipschitz_affineMatVec_of_rowSumContraction hI hA b

/--
[lipschitz_affineMatVec_of_columnSumContraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma lipschitz_affineMatVec_of_columnSumContraction_eq
  {n : ℕ}
  {I : RatInterval.IntervalMatrix n n}
  {A : Fin n → Fin n → ℝ}
  {b : Fin n → ℝ}
-- given
  (hI : RatInterval.ColumnSumContraction I)
  (hA : RatInterval.MatrixMem A I) :
-- imply
  LipschitzWithConstant (fun x i => RatInterval.matVec A x i + b i) (hI.c : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.lipschitz_affineMatVec_of_columnSumContraction hI hA b

/--
[l1Dist_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma l1Dist_triangle_eq
  {n : ℕ}
  {x y z : Fin n → ℝ} :
-- imply
  l1Dist x z ≤ l1Dist x y + l1Dist y z := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.l1Dist_triangle x y z

/--
[l1Dist_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma l1Dist_self_eq
  {n : ℕ}
  {x : Fin n → ℝ} :
-- imply
  l1Dist x x = 0 := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.l1Dist_self x

/--
[l1Dist_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma l1Dist_eq_zero_iff_eq
  {n : ℕ}
  {x y : Fin n → ℝ} :
-- imply
  l1Dist x y = 0 ↔ x = y := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.l1Dist_eq_zero_iff

/--
[l1Dist_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma l1Dist_comm_eq
  {n : ℕ}
  {x y : Fin n → ℝ} :
-- imply
  l1Dist x y = l1Dist y x := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.l1Dist_comm x y

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma ext_eq
  {n : ℕ}
  {x y : L1Vector n}
-- given
  (h : x.coord = y.coord) :
-- imply
  x = y := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.L1Vector.ext h

/--
[pi_dist_le_l1Dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma pi_dist_le_l1Dist_eq
  {n : ℕ}
  {n : ℕ}
  {x y : Fin n → ℝ} :
-- imply
  dist x y ≤ l1Dist x y := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.L1Vector.pi_dist_le_l1Dist x y

/--
[l1Dist_le_nat_mul_pi_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma l1Dist_le_nat_mul_pi_dist_eq
  {n : ℕ}
  {n : ℕ}
  {x y : Fin n → ℝ} :
-- imply
  l1Dist x y ≤ (n : ℝ) * dist x y := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.L1Vector.l1Dist_le_nat_mul_pi_dist x y

/--
[lipschitz_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma lipschitz_coord_eq
  {n : ℕ}
  {n : ℕ} :
-- imply
  LipschitzWith 1 (fun x : L1Vector n => x.coord) := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.L1Vector.lipschitz_coord

/--
[lipschitz_ofFun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma lipschitz_ofFun_eq
  {n : ℕ}
  {n : ℕ} :
-- imply
  LipschitzWith (n : NNReal) (ofFun : (Fin n → ℝ) → L1Vector n) := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.L1Vector.lipschitz_ofFun

/--
[isUniformEmbedding_equivFun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma isUniformEmbedding_equivFun_eq
  {n : ℕ}
  {n : ℕ} :
-- imply
  IsUniformEmbedding (equivFun n) := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.L1Vector.isUniformEmbedding_equivFun n

/--
[contractingWith_liftMap_of_l1_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma contractingWith_liftMap_of_l1_contraction_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {c : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hLip : LipschitzWithConstant F c) :
-- imply
  ContractingWith (⟨c, hc_nonneg⟩ : NNReal) (L1Vector.liftMap F) := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.contractingWith_liftMap_of_l1_contraction hc_nonneg hc_lt_one hLip

/--
[certifiedFixedPointOfL1Contraction_isFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma certifiedFixedPointOfL1Contraction_isFixed_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {c : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hLip : LipschitzWithConstant F c) :
-- imply
  F (certifiedFixedPointOfL1Contraction F hc_nonneg hc_lt_one hLip) = certifiedFixedPointOfL1Contraction F hc_nonneg hc_lt_one hLip := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.certifiedFixedPointOfL1Contraction_isFixed F hc_nonneg hc_lt_one hLip

/--
[exists_fixedPoint_of_l1_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma exists_fixedPoint_of_l1_contraction_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {c : ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hc_lt_one : c < 1)
  (hLip : LipschitzWithConstant F c) :
-- imply
  ∃ p : Fin n → ℝ, F p = p := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.exists_fixedPoint_of_l1_contraction F hc_nonneg hc_lt_one hLip

/--
[lipschitz_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma lipschitz_iterate_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {c : ℝ}
  {k : ℕ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hLip : LipschitzWithConstant F c) :
-- imply
  LipschitzWithConstant (iterate F k) (c ^ k) := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.lipschitz_iterate hc_nonneg hLip k

/--
[mapsClosedBall_iterate_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma mapsClosedBall_iterate_mem_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {center : Fin n → ℝ}
  {radius : ℝ}
  {x : Fin n → ℝ}
  {k : ℕ}
-- given
  (hmap : MapsClosedBall F center radius)
  (hx : ClosedBall center radius x) :
-- imply
  ClosedBall center radius (iterate F k x) := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.mapsClosedBall_iterate_mem hmap hx k

/--
[mapsClosedBall_of_residual_and_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma mapsClosedBall_of_residual_and_lipschitz_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {c radius : ℝ}
  {center : Fin n → ℝ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hLip : LipschitzWithConstant F c)
  (hresidual : l1Dist (F center) center ≤ (1 - c) * radius) :
-- imply
  MapsClosedBall F center radius := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.mapsClosedBall_of_residual_and_lipschitz F center hc_nonneg hLip hresidual

/--
[center_mem_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma center_mem_closedBall_eq
  {n : ℕ}
  {center : Fin n → ℝ}
  {radius : ℝ}
-- given
  (hradius : 0 ≤ radius) :
-- imply
  ClosedBall center radius center := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.center_mem_closedBall center hradius

/--
[closedBall_mono_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma closedBall_mono_radius_eq
  {n : ℕ}
  {center x : Fin n → ℝ}
  {radius radius' : ℝ}
-- given
  (hx : ClosedBall center radius x)
  (hradius : radius ≤ radius') :
-- imply
  ClosedBall center radius' x := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.closedBall_mono_radius hx hradius

/--
[mapsClosedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma mapsClosedBall_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {C : ClosedBallContractionCertificate F} :
-- imply
  MapsClosedBall F C.center C.radius := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ClosedBallContractionCertificate.mapsClosedBall C

/--
[center_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma center_mem_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {C : ClosedBallContractionCertificate F} :
-- imply
  ClosedBall C.center C.radius C.center := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ClosedBallContractionCertificate.center_mem C

/--
[residual_l1Dist_le_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma residual_l1Dist_le_margin_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {C : ClosedBallContractionCertificate F} :
-- imply
  l1Dist (F C.center) C.center ≤ (1 - C.c) * C.radius := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ClosedBallContractionCertificate.residual_l1Dist_le_margin C

/--
[residual_plus_mul_le_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma residual_plus_mul_le_radius_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {C : ClosedBallContractionCertificate F} :
-- imply
  l1Dist (F C.center) C.center + C.c * C.radius ≤ C.radius := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ClosedBallContractionCertificate.residual_plus_mul_le_radius C

/--
[with_larger_radius_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma with_larger_radius_center_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {C : ClosedBallContractionCertificate F}
  {radius' : ℝ}
-- given
  (hradius : C.radius ≤ radius') :
-- imply
  (C.with_larger_radius hradius).center = C.center := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ClosedBallContractionCertificate.with_larger_radius_center C hradius

/--
[with_larger_radius_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma with_larger_radius_radius_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {C : ClosedBallContractionCertificate F}
  {radius' : ℝ}
-- given
  (hradius : C.radius ≤ radius') :
-- imply
  (C.with_larger_radius hradius).radius = radius' := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ClosedBallContractionCertificate.with_larger_radius_radius C hradius

/--
[with_larger_radius_c](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma with_larger_radius_c_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {C : ClosedBallContractionCertificate F}
  {radius' : ℝ}
-- given
  (hradius : C.radius ≤ radius') :
-- imply
  (C.with_larger_radius hradius).c = C.c := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ClosedBallContractionCertificate.with_larger_radius_c C hradius

/--
[fixedPoint_unique_of_l1_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma fixedPoint_unique_of_l1_contraction_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {c : ℝ}
  {x y : Fin n → ℝ}
-- given
  (hc : c < 1)
  (hLip : LipschitzWithConstant F c)
  (hx : F x = x)
  (hy : F y = y) :
-- imply
  x = y := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.fixedPoint_unique_of_l1_contraction F hc hLip hx hy

/--
[iterate_eq_of_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma iterate_eq_of_fixed_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {x : Fin n → ℝ}
  {k : ℕ}
-- given
  (hx : F x = x) :
-- imply
  iterate F k x = x := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.iterate_eq_of_fixed hx k

/--
[iterate_l1Dist_le_pow_mul_of_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma iterate_l1Dist_le_pow_mul_of_fixed_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {c : ℝ}
  {p : Fin n → ℝ}
  {x : Fin n → ℝ}
  {k : ℕ}
-- given
  (hc_nonneg : 0 ≤ c)
  (hLip : LipschitzWithConstant F c)
  (hp : F p = p) :
-- imply
  l1Dist (iterate F k x) p ≤ c ^ k * l1Dist x p := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.iterate_l1Dist_le_pow_mul_of_fixed hc_nonneg hLip hp x k

/--
[with_larger_radius_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma with_larger_radius_fixedPoint_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {C : ClosedBallContractionCertificate F}
  {radius' : ℝ}
-- given
  (hradius : C.radius ≤ radius') :
-- imply
  (C.with_larger_radius hradius).fixedPoint = C.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ClosedBallContractionCertificate.with_larger_radius_fixedPoint C hradius

/--
[fixedPoint_isFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma fixedPoint_isFixed_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {C : ClosedBallContractionCertificate F} :
-- imply
  F C.fixedPoint = C.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ClosedBallContractionCertificate.fixedPoint_isFixed C

/--
[fixedPoint_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma fixedPoint_unique_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {C : ClosedBallContractionCertificate F}
  {x y : Fin n → ℝ}
-- given
  (hx : F x = x)
  (hy : F y = y) :
-- imply
  x = y := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ClosedBallContractionCertificate.fixedPoint_unique C hx hy

/--
[fixedPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma fixedPoint_mem_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {C : ClosedBallContractionCertificate F}
  {x : Fin n → ℝ}
-- given
  (hx : F x = x) :
-- imply
  ClosedBall C.center C.radius x := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ClosedBallContractionCertificate.fixedPoint_mem C hx

/--
[fixedPoint_mem_selected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma fixedPoint_mem_selected_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {C : ClosedBallContractionCertificate F} :
-- imply
  ClosedBall C.center C.radius C.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ClosedBallContractionCertificate.fixedPoint_mem_selected C

/--
[fixedPoint_mem_of_radius_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma fixedPoint_mem_of_radius_le_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {C : ClosedBallContractionCertificate F}
  {radius' : ℝ}
-- given
  (hradius : C.radius ≤ radius') :
-- imply
  ClosedBall C.center radius' C.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ClosedBallContractionCertificate.fixedPoint_mem_of_radius_le C hradius

/--
[exists_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma exists_fixedPoint_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {C : ClosedBallContractionCertificate F} :
-- imply
  ∃ p : Fin n → ℝ, F p = p ∧ ClosedBall C.center C.radius p := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ClosedBallContractionCertificate.exists_fixedPoint C

/--
[exists_unique_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma exists_unique_fixedPoint_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {C : ClosedBallContractionCertificate F} :
-- imply
  ∃! p : Fin n → ℝ, F p = p := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ClosedBallContractionCertificate.exists_unique_fixedPoint C

/--
[eq_fixedPoint_of_isFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma eq_fixedPoint_of_isFixed_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {C : ClosedBallContractionCertificate F}
  {x : Fin n → ℝ}
-- given
  (hx : F x = x) :
-- imply
  x = C.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ClosedBallContractionCertificate.eq_fixedPoint_of_isFixed C hx

/--
[iterate_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma iterate_mem_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {C : ClosedBallContractionCertificate F}
  {x : Fin n → ℝ}
  {k : ℕ}
-- given
  (hx : ClosedBall C.center C.radius x) :
-- imply
  ClosedBall C.center C.radius (FiniteContraction.iterate F k x) := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ClosedBallContractionCertificate.iterate_mem C hx k

/--
[iterate_mem_of_radius_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma iterate_mem_of_radius_le_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {C : ClosedBallContractionCertificate F}
  {radius' : ℝ}
  {x : Fin n → ℝ}
  {k : ℕ}
-- given
  (hradius : C.radius ≤ radius')
  (hx : ClosedBall C.center radius' x) :
-- imply
  ClosedBall C.center radius' (FiniteContraction.iterate F k x) := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ClosedBallContractionCertificate.iterate_mem_of_radius_le C hradius hx k

/--
[iterate_l1Dist_le_pow_mul_of_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma iterate_l1Dist_le_pow_mul_of_fixed_eq_2
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {C : ClosedBallContractionCertificate F}
  {p : Fin n → ℝ}
  {x : Fin n → ℝ}
  {k : ℕ}
-- given
  (hp : F p = p) :
-- imply
  l1Dist (FiniteContraction.iterate F k x) p ≤ C.c ^ k * l1Dist x p := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ClosedBallContractionCertificate.iterate_l1Dist_le_pow_mul_of_fixed C hp x k

/--
[iterate_l1Dist_le_pow_mul_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma iterate_l1Dist_le_pow_mul_fixedPoint_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {C : ClosedBallContractionCertificate F}
  {x : Fin n → ℝ}
  {k : ℕ} :
-- imply
  l1Dist (FiniteContraction.iterate F k x) C.fixedPoint ≤ C.c ^ k * l1Dist x C.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ClosedBallContractionCertificate.iterate_l1Dist_le_pow_mul_fixedPoint C x k

/--
[matVec_fixedPoint_unique_of_rowSumContraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma matVec_fixedPoint_unique_of_rowSumContraction_eq
  {n : ℕ}
  {I : RatInterval.IntervalMatrix n n}
  {A : Fin n → Fin n → ℝ}
  {x y : Fin n → ℝ}
-- given
  (hI : RatInterval.RowSumContraction I)
  (hA : RatInterval.MatrixMem A I)
  (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
  (hx : (fun x i => RatInterval.matVec A x i) x = x)
  (hy : (fun x i => RatInterval.matVec A x i) y = y) :
-- imply
  x = y := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.matVec_fixedPoint_unique_of_rowSumContraction hI hA hcontract hx hy

/--
[matVec_fixedPoint_unique_of_columnSumContraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma matVec_fixedPoint_unique_of_columnSumContraction_eq
  {n : ℕ}
  {I : RatInterval.IntervalMatrix n n}
  {A : Fin n → Fin n → ℝ}
  {x y : Fin n → ℝ}
-- given
  (hI : RatInterval.ColumnSumContraction I)
  (hA : RatInterval.MatrixMem A I)
  (hx : (fun x i => RatInterval.matVec A x i) x = x)
  (hy : (fun x i => RatInterval.matVec A x i) y = y) :
-- imply
  x = y := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.matVec_fixedPoint_unique_of_columnSumContraction hI hA hx hy

/--
[affineMap_fixedPoint_unique_of_rowSumContraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma affineMap_fixedPoint_unique_of_rowSumContraction_eq
  {n : ℕ}
  {I : RatInterval.IntervalMatrix n n}
  {A : Fin n → Fin n → ℝ}
  {b : Fin n → ℝ}
  {x y : Fin n → ℝ}
-- given
  (hI : RatInterval.RowSumContraction I)
  (hA : RatInterval.MatrixMem A I)
  (hcontract : (n : ℝ) * (hI.c : ℝ) < 1)
  (hx : (fun x i => RatInterval.affineMap A b x i) x = x)
  (hy : (fun x i => RatInterval.affineMap A b x i) y = y) :
-- imply
  x = y := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.affineMap_fixedPoint_unique_of_rowSumContraction hI hA b hcontract hx hy

/--
[affineMap_fixedPoint_unique_of_columnSumContraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma affineMap_fixedPoint_unique_of_columnSumContraction_eq
  {n : ℕ}
  {I : RatInterval.IntervalMatrix n n}
  {A : Fin n → Fin n → ℝ}
  {b : Fin n → ℝ}
  {x y : Fin n → ℝ}
-- given
  (hI : RatInterval.ColumnSumContraction I)
  (hA : RatInterval.MatrixMem A I)
  (hx : (fun x i => RatInterval.affineMap A b x i) x = x)
  (hy : (fun x i => RatInterval.affineMap A b x i) y = y) :
-- imply
  x = y := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.affineMap_fixedPoint_unique_of_columnSumContraction hI hA b hx hy

/--
[residual_l1Dist_le_of_vectorMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma residual_l1Dist_le_of_vectorMem_eq
  {n : ℕ}
  {F : (Fin n → ℝ) → Fin n → ℝ}
  {center : Fin n → ℝ}
  {R : RatInterval.IntervalVector n}
-- given
  (hR : RatInterval.VectorMem (fun i => F center i - center i) R) :
-- imply
  l1Dist (F center) center ≤ (RatInterval.VectorAbsSum R : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.residual_l1Dist_le_of_vectorMem hR

/--
[zeroMap_lipschitz_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma zeroMap_lipschitz_zero_eq
  {n : ℕ} :
-- imply
  LipschitzWithConstant (@zeroMap n) 0 := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.zeroMap_lipschitz_zero

/--
[zeroMap_mapsClosedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma zeroMap_mapsClosedBall_eq
  {n : ℕ}
  {radius : ℝ}
-- given
  (hradius : 0 ≤ radius) :
-- imply
  MapsClosedBall (@zeroMap n) 0 radius := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.zeroMap_mapsClosedBall hradius

/--
[zeroMap_fixedPoint_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma zeroMap_fixedPoint_eq_zero_eq
  {n : ℕ}
  {x : Fin n → ℝ}
-- given
  (hx : zeroMap x = x) :
-- imply
  x = 0 := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.zeroMap_fixedPoint_eq_zero hx

/--
[matrix_mem_intervals](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma matrix_mem_intervals_eq :
-- imply
  RatInterval.MatrixMem matrix intervals := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.NonzeroAffineExample.matrix_mem_intervals

/--
[offset_mem_intervals](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma offset_mem_intervals_eq :
-- imply
  RatInterval.VectorMem offset offsetIntervals := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.NonzeroAffineExample.offset_mem_intervals

/--
[intervals_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma intervals_nonnegative_eq :
-- imply
  RatInterval.MatrixNonnegative intervals := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.NonzeroAffineExample.intervals_nonnegative

/--
[centerQ_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma centerQ_nonnegative_eq
  {i : Fin 1} :
-- imply
  0 ≤ centerQ i := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.NonzeroAffineExample.centerQ_nonnegative i

/--
[center_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma center_fixedPoint_eq :
-- imply
  (fun x i => RatInterval.affineMap matrix offset x i) (fun _ : Fin 1 => (1 / 2 : ℝ)) = (fun _ : Fin 1 => (1 / 2 : ℝ)) := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.NonzeroAffineExample.center_fixedPoint

/--
[affineResidual_absSum_le_radius_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma affineResidual_absSum_le_radius_one_eq :
-- imply
  (RatInterval.VectorAbsSum (RatInterval.matrixVectorAffineResidual intervals offsetIntervals (RatInterval.pointVector centerQ)) : ℝ) ≤ (1 - (columnSumContraction.c : ℝ)) * (1 : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.NonzeroAffineExample.affineResidual_absSum_le_radius_one

/--
[affineResidualNonneg_absSum_le_radius_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma affineResidualNonneg_absSum_le_radius_zero_eq :
-- imply
  (RatInterval.VectorAbsSum (RatInterval.matrixVectorAffineResidualNonneg intervals offsetIntervals (RatInterval.pointVector centerQ) intervals_nonnegative (RatInterval.pointVector_nonnegative centerQ_nonnegative)) : ℝ) ≤ (1 - (columnSumContraction.c : ℝ)) * (0 : ℝ) := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.NonzeroAffineExample.affineResidualNonneg_absSum_le_radius_zero

/--
[exists_fixedPoint_in_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma exists_fixedPoint_in_ball_eq :
-- imply
  ∃ p : Fin 1 → ℝ, (fun x i => RatInterval.affineMap matrix offset x i) p = p ∧ ClosedBall (fun _ : Fin 1 => (1 / 2 : ℝ)) 1 p := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.NonzeroAffineExample.exists_fixedPoint_in_ball

/--
[exists_fixedPoint_in_exact_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma exists_fixedPoint_in_exact_ball_eq :
-- imply
  ∃ p : Fin 1 → ℝ, (fun x i => RatInterval.affineMap matrix offset x i) p = p ∧ ClosedBall (fun _ : Fin 1 => (1 / 2 : ℝ)) 0 p := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.NonzeroAffineExample.exists_fixedPoint_in_exact_ball

/--
[exists_fixedPoint_in_relaxed_exact_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma exists_fixedPoint_in_relaxed_exact_ball_eq :
-- imply
  ∃ p : Fin 1 → ℝ, (fun x i => RatInterval.affineMap matrix offset x i) p = p ∧ ClosedBall (fun _ : Fin 1 => (1 / 2 : ℝ)) 1 p := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.NonzeroAffineExample.exists_fixedPoint_in_relaxed_exact_ball

/--
[selectedFixedPoint_eq_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma selectedFixedPoint_eq_center_eq :
-- imply
  affineRationalCenterClosedBallCertificate.fixedPoint = (fun _ : Fin 1 => (1 / 2 : ℝ)) := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.NonzeroAffineExample.selectedFixedPoint_eq_center

/--
[selectedExactFixedPoint_eq_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma selectedExactFixedPoint_eq_center_eq :
-- imply
  affineRationalCenterExactClosedBallCertificate.fixedPoint = (fun _ : Fin 1 => (1 / 2 : ℝ)) := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.NonzeroAffineExample.selectedExactFixedPoint_eq_center

/--
[matrix_mem_intervals](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma matrix_mem_intervals_eq_2 :
-- imply
  RatInterval.MatrixMem matrix intervals := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ZeroLinearExample.matrix_mem_intervals

/--
[offset_mem_intervals](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma offset_mem_intervals_eq_2 :
-- imply
  RatInterval.VectorMem offset offsetIntervals := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ZeroLinearExample.offset_mem_intervals

/--
[residual_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma residual_mem_eq :
-- imply
  RatInterval.VectorMem (fun i => RatInterval.matVec matrix (0 : Fin 1 → ℝ) i - (0 : Fin 1 → ℝ) i) residualIntervals := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ZeroLinearExample.residual_mem

/--
[mapsClosedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma mapsClosedBall_eq_2
  {radius : ℝ}
-- given
  (hradius : 0 ≤ radius) :
-- imply
  MapsClosedBall (fun x i => RatInterval.matVec matrix x i) (0 : Fin 1 → ℝ) radius := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ZeroLinearExample.mapsClosedBall hradius

/--
[mapsClosedBall_from_rationalCenter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma mapsClosedBall_from_rationalCenter_eq
  {radius : ℝ}
-- given
  (hradius : 0 ≤ radius) :
-- imply
  MapsClosedBall (fun x i => RatInterval.matVec matrix x i) (fun _ : Fin 1 => (0 : ℝ)) radius := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ZeroLinearExample.mapsClosedBall_from_rationalCenter hradius

/--
[mapsClosedBall_from_affineRationalCenter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean)
-/
@[path]
private lemma mapsClosedBall_from_affineRationalCenter_eq
  {radius : ℝ}
-- given
  (hradius : 0 ≤ radius) :
-- imply
  MapsClosedBall (fun x i => RatInterval.affineMap matrix offset x i) (fun _ : Fin 1 => (0 : ℝ)) radius := by
-- proof
  apply StatMech.Exact3D.FiniteContraction.ZeroLinearExample.mapsClosedBall_from_affineRationalCenter hradius


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.Intervals
open StatMech StatMech.Exact3D StatMech.Exact3D.RatInterval


/--
[memQ_def](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma memQ_def_eq
  {I : RatInterval}
  {q : ℚ} :
-- imply
  I.MemQ q ↔ I.lower ≤ q ∧ q ≤ I.upper := by
-- proof
  apply StatMech.Exact3D.RatInterval.memQ_def I q

/--
[memR_def](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma memR_def_eq
  {I : RatInterval}
  {x : ℝ} :
-- imply
  I.MemR x ↔ (I.lower : ℝ) ≤ x ∧ x ≤ (I.upper : ℝ) := by
-- proof
  apply StatMech.Exact3D.RatInterval.memR_def I x

/--
[width_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma width_nonneg_eq
  {I : RatInterval} :
-- imply
  0 ≤ I.width := by
-- proof
  apply StatMech.Exact3D.RatInterval.width_nonneg I

/--
[absUpper_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma absUpper_nonneg_eq
  {I : RatInterval} :
-- imply
  0 ≤ I.absUpper := by
-- proof
  apply StatMech.Exact3D.RatInterval.absUpper_nonneg I

/--
[absUpper_point](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma absUpper_point_eq
  {q : ℚ} :
-- imply
  (point q).absUpper = |q| := by
-- proof
  apply StatMech.Exact3D.RatInterval.absUpper_point q

/--
[add_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma add_nonnegative_eq
  {I J : RatInterval}
-- given
  (hI : I.Nonnegative)
  (hJ : J.Nonnegative) :
-- imply
  (add I J).Nonnegative := by
-- proof
  apply StatMech.Exact3D.RatInterval.add_nonnegative hI hJ

/--
[finsetSum_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma finsetSum_nonnegative_eq
  {s : Finset α}
  {I : α → RatInterval}
-- given
  (hI : ∀ a, a ∈ s → (I a).Nonnegative) :
-- imply
  (finsetSum s I).Nonnegative := by
-- proof
  apply StatMech.Exact3D.RatInterval.finsetSum_nonnegative hI

/--
[mulNonneg_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma mulNonneg_nonnegative_eq
  {I J : RatInterval}
-- given
  (hI : I.Nonnegative)
  (hJ : J.Nonnegative) :
-- imply
  (mulNonneg I J hI hJ).Nonnegative := by
-- proof
  apply StatMech.Exact3D.RatInterval.mulNonneg_nonnegative hI hJ

/--
[point_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma point_memQ_eq
  {q : ℚ} :
-- imply
  (point q).MemQ q := by
-- proof
  apply StatMech.Exact3D.RatInterval.point_memQ q

/--
[point_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma point_memR_eq
  {q : ℚ} :
-- imply
  (point q).MemR (q : ℝ) := by
-- proof
  apply StatMech.Exact3D.RatInterval.point_memR q

/--
[memR_of_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma memR_of_memQ_eq
  {I : RatInterval}
  {q : ℚ}
-- given
  (hq : I.MemQ q) :
-- imply
  I.MemR (q : ℝ) := by
-- proof
  apply StatMech.Exact3D.RatInterval.memR_of_memQ hq

/--
[point_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma point_nonnegative_eq
  {q : ℚ}
-- given
  (hq : 0 ≤ q) :
-- imply
  (point q).Nonnegative := by
-- proof
  apply StatMech.Exact3D.RatInterval.point_nonnegative hq

/--
[add_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma add_memQ_eq
  {I J : RatInterval}
  {x y : ℚ}
-- given
  (hx : I.MemQ x)
  (hy : J.MemQ y) :
-- imply
  (add I J).MemQ (x + y) := by
-- proof
  apply StatMech.Exact3D.RatInterval.add_memQ hx hy

/--
[add_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma add_memR_eq
  {I J : RatInterval}
  {x y : ℝ}
-- given
  (hx : I.MemR x)
  (hy : J.MemR y) :
-- imply
  (add I J).MemR (x + y) := by
-- proof
  apply StatMech.Exact3D.RatInterval.add_memR hx hy

/--
[neg_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma neg_memQ_eq
  {I : RatInterval}
  {x : ℚ}
-- given
  (hx : I.MemQ x) :
-- imply
  (neg I).MemQ (-x) := by
-- proof
  apply StatMech.Exact3D.RatInterval.neg_memQ hx

/--
[neg_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma neg_memR_eq
  {I : RatInterval}
  {x : ℝ}
-- given
  (hx : I.MemR x) :
-- imply
  (neg I).MemR (-x) := by
-- proof
  apply StatMech.Exact3D.RatInterval.neg_memR hx

/--
[sub_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma sub_memQ_eq
  {I J : RatInterval}
  {x y : ℚ}
-- given
  (hx : I.MemQ x)
  (hy : J.MemQ y) :
-- imply
  (sub I J).MemQ (x - y) := by
-- proof
  apply StatMech.Exact3D.RatInterval.sub_memQ hx hy

/--
[sub_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma sub_memR_eq
  {I J : RatInterval}
  {x y : ℝ}
-- given
  (hx : I.MemR x)
  (hy : J.MemR y) :
-- imply
  (sub I J).MemR (x - y) := by
-- proof
  apply StatMech.Exact3D.RatInterval.sub_memR hx hy

/--
[finsetSum_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma finsetSum_memQ_eq
  {s : Finset α}
  {I : α → RatInterval}
  {x : α → ℚ}
-- given
  (hx : ∀ a, a ∈ s → (I a).MemQ (x a)) :
-- imply
  (finsetSum s I).MemQ (s.sum fun a => x a) := by
-- proof
  apply StatMech.Exact3D.RatInterval.finsetSum_memQ hx

/--
[finsetSum_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma finsetSum_memR_eq
  {s : Finset α}
  {I : α → RatInterval}
  {x : α → ℝ}
-- given
  (hx : ∀ a, a ∈ s → (I a).MemR (x a)) :
-- imply
  (finsetSum s I).MemR (s.sum fun a => x a) := by
-- proof
  apply StatMech.Exact3D.RatInterval.finsetSum_memR hx

/--
[abs_le_absUpper_of_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma abs_le_absUpper_of_memQ_eq
  {I : RatInterval}
  {q : ℚ}
-- given
  (hq : I.MemQ q) :
-- imply
  |q| ≤ I.absUpper := by
-- proof
  apply StatMech.Exact3D.RatInterval.abs_le_absUpper_of_memQ hq

/--
[abs_le_absUpper_of_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma abs_le_absUpper_of_memR_eq
  {I : RatInterval}
  {x : ℝ}
-- given
  (hx : I.MemR x) :
-- imply
  |x| ≤ (I.absUpper : ℝ) := by
-- proof
  apply StatMech.Exact3D.RatInterval.abs_le_absUpper_of_memR hx

/--
[mul_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma mul_memR_eq
  {I J : RatInterval}
  {x y : ℝ}
-- given
  (hx : I.MemR x)
  (hy : J.MemR y) :
-- imply
  (mul I J).MemR (x * y) := by
-- proof
  apply StatMech.Exact3D.RatInterval.mul_memR hx hy

/--
[mul_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma mul_memQ_eq
  {I J : RatInterval}
  {x y : ℚ}
-- given
  (hx : I.MemQ x)
  (hy : J.MemQ y) :
-- imply
  (mul I J).MemQ (x * y) := by
-- proof
  apply StatMech.Exact3D.RatInterval.mul_memQ hx hy

/--
[mulNonneg_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma mulNonneg_memQ_eq
  {I J : RatInterval}
  {x y : ℚ}
-- given
  (hI : I.Nonnegative)
  (hJ : J.Nonnegative)
  (hx : I.MemQ x)
  (hy : J.MemQ y) :
-- imply
  (mulNonneg I J hI hJ).MemQ (x * y) := by
-- proof
  apply StatMech.Exact3D.RatInterval.mulNonneg_memQ hI hJ hx hy

/--
[mulNonneg_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma mulNonneg_memR_eq
  {I J : RatInterval}
  {x y : ℝ}
-- given
  (hI : I.Nonnegative)
  (hJ : J.Nonnegative)
  (hx : I.MemR x)
  (hy : J.MemR y) :
-- imply
  (mulNonneg I J hI hJ).MemR (x * y) := by
-- proof
  apply StatMech.Exact3D.RatInterval.mulNonneg_memR hI hJ hx hy

/--
[MatrixMemQ.memR_coe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma memR_coe_eq
  {m n : ℕ}
  {A : Fin m → Fin n → ℚ}
  {I : IntervalMatrix m n}
-- given
  (hA : MatrixMemQ A I) :
-- imply
  MatrixMem (fun i j => (A i j : ℝ)) I := by
-- proof
  apply StatMech.Exact3D.RatInterval.MatrixMemQ.memR_coe hA

/--
[VectorMemQ.memR_coe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma memR_coe_eq_2
  {n : ℕ}
  {x : Fin n → ℚ}
  {I : IntervalVector n}
-- given
  (hx : VectorMemQ x I) :
-- imply
  VectorMem (fun i => (x i : ℝ)) I := by
-- proof
  apply StatMech.Exact3D.RatInterval.VectorMemQ.memR_coe hx

/--
[VectorAbsSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma VectorAbsSum_nonneg_eq
  {n : ℕ}
  {I : IntervalVector n} :
-- imply
  0 ≤ VectorAbsSum I := by
-- proof
  apply StatMech.Exact3D.RatInterval.VectorAbsSum_nonneg I

/--
[VectorAbsSum_nonneg_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma VectorAbsSum_nonneg_real_eq
  {n : ℕ}
  {I : IntervalVector n} :
-- imply
  0 ≤ (VectorAbsSum I : ℝ) := by
-- proof
  apply StatMech.Exact3D.RatInterval.VectorAbsSum_nonneg_real I

/--
[VectorAbsSum_le_of_absUpper_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma VectorAbsSum_le_of_absUpper_le_eq
  {n : ℕ}
  {I J : IntervalVector n}
-- given
  (h : ∀ i, (I i).absUpper ≤ (J i).absUpper) :
-- imply
  VectorAbsSum I ≤ VectorAbsSum J := by
-- proof
  apply StatMech.Exact3D.RatInterval.VectorAbsSum_le_of_absUpper_le h

/--
[vectorAdd_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma vectorAdd_nonnegative_eq
  {n : ℕ}
  {I J : IntervalVector n}
-- given
  (hI : VectorNonnegative I)
  (hJ : VectorNonnegative J) :
-- imply
  VectorNonnegative (vectorAdd I J) := by
-- proof
  apply StatMech.Exact3D.RatInterval.vectorAdd_nonnegative hI hJ

/--
[pointVector_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma pointVector_apply_eq
  {n : ℕ}
  {x : Fin n → ℚ}
  {i : Fin n} :
-- imply
  pointVector x i = point (x i) := by
-- proof
  apply StatMech.Exact3D.RatInterval.pointVector_apply x i

/--
[pointMatrix_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma pointMatrix_apply_eq
  {m n : ℕ}
  {A : Fin m → Fin n → ℚ}
  {i : Fin m}
  {j : Fin n} :
-- imply
  pointMatrix A i j = point (A i j) := by
-- proof
  apply StatMech.Exact3D.RatInterval.pointMatrix_apply A i j

/--
[pointVector_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma pointVector_nonnegative_eq
  {n : ℕ}
  {x : Fin n → ℚ}
-- given
  (hx : ∀ i, 0 ≤ x i) :
-- imply
  VectorNonnegative (pointVector x) := by
-- proof
  apply StatMech.Exact3D.RatInterval.pointVector_nonnegative hx

/--
[pointMatrix_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma pointMatrix_nonnegative_eq
  {m n : ℕ}
  {A : Fin m → Fin n → ℚ}
-- given
  (hA : ∀ i j, 0 ≤ A i j) :
-- imply
  MatrixNonnegative (pointMatrix A) := by
-- proof
  apply StatMech.Exact3D.RatInterval.pointMatrix_nonnegative hA

/--
[VectorAbsSum_pointVector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma VectorAbsSum_pointVector_eq
  {n : ℕ}
  {x : Fin n → ℚ} :
-- imply
  VectorAbsSum (pointVector x) = ∑ i, |x i| := by
-- proof
  apply StatMech.Exact3D.RatInterval.VectorAbsSum_pointVector x

/--
[MatrixAbsRowSum_pointMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma MatrixAbsRowSum_pointMatrix_eq
  {m n : ℕ}
  {A : Fin m → Fin n → ℚ}
  {i : Fin m} :
-- imply
  MatrixAbsRowSum (pointMatrix A) i = ∑ j, |A i j| := by
-- proof
  apply StatMech.Exact3D.RatInterval.MatrixAbsRowSum_pointMatrix A i

/--
[MatrixAbsColSum_pointMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma MatrixAbsColSum_pointMatrix_eq
  {m n : ℕ}
  {A : Fin m → Fin n → ℚ}
  {j : Fin n} :
-- imply
  MatrixAbsColSum (pointMatrix A) j = ∑ i, |A i j| := by
-- proof
  apply StatMech.Exact3D.RatInterval.MatrixAbsColSum_pointMatrix A j

/--
[MatrixMem.row_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma row_sum_le_eq
  {m n : ℕ}
  {A : Fin m → Fin n → ℝ}
  {I : IntervalMatrix m n}
  {i : Fin m}
-- given
  (hA : MatrixMem A I) :
-- imply
  (∑ j, A i j) ≤ (MatrixUpperRowSum I i : ℝ) := by
-- proof
  apply StatMech.Exact3D.RatInterval.MatrixMem.row_sum_le hA i

/--
[MatrixMem.row_abs_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma row_abs_sum_le_eq
  {m n : ℕ}
  {A : Fin m → Fin n → ℝ}
  {I : IntervalMatrix m n}
  {i : Fin m}
-- given
  (hA : MatrixMem A I) :
-- imply
  (∑ j, |A i j|) ≤ (MatrixAbsRowSum I i : ℝ) := by
-- proof
  apply StatMech.Exact3D.RatInterval.MatrixMem.row_abs_sum_le hA i

/--
[MatrixMem.col_abs_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma col_abs_sum_le_eq
  {m n : ℕ}
  {A : Fin m → Fin n → ℝ}
  {I : IntervalMatrix m n}
  {j : Fin n}
-- given
  (hA : MatrixMem A I) :
-- imply
  (∑ i, |A i j|) ≤ (MatrixAbsColSum I j : ℝ) := by
-- proof
  apply StatMech.Exact3D.RatInterval.MatrixMem.col_abs_sum_le hA j

/--
[VectorMem.abs_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma abs_sum_le_eq
  {n : ℕ}
  {x : Fin n → ℝ}
  {I : IntervalVector n}
-- given
  (hx : VectorMem x I) :
-- imply
  (∑ i, |x i|) ≤ (VectorAbsSum I : ℝ) := by
-- proof
  apply StatMech.Exact3D.RatInterval.VectorMem.abs_sum_le hx

/--
[vectorAdd_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma vectorAdd_memR_eq
  {n : ℕ}
  {x y : Fin n → ℝ}
  {I J : IntervalVector n}
-- given
  (hx : VectorMem x I)
  (hy : VectorMem y J) :
-- imply
  VectorMem (fun i => x i + y i) (vectorAdd I J) := by
-- proof
  apply StatMech.Exact3D.RatInterval.vectorAdd_memR hx hy

/--
[vectorNeg_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma vectorNeg_memR_eq
  {n : ℕ}
  {x : Fin n → ℝ}
  {I : IntervalVector n}
-- given
  (hx : VectorMem x I) :
-- imply
  VectorMem (fun i => -x i) (vectorNeg I) := by
-- proof
  apply StatMech.Exact3D.RatInterval.vectorNeg_memR hx

/--
[vectorSub_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma vectorSub_memR_eq
  {n : ℕ}
  {x y : Fin n → ℝ}
  {I J : IntervalVector n}
-- given
  (hx : VectorMem x I)
  (hy : VectorMem y J) :
-- imply
  VectorMem (fun i => x i - y i) (vectorSub I J) := by
-- proof
  apply StatMech.Exact3D.RatInterval.vectorSub_memR hx hy

/--
[vectorAdd_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma vectorAdd_memQ_eq
  {n : ℕ}
  {x y : Fin n → ℚ}
  {I J : IntervalVector n}
-- given
  (hx : VectorMemQ x I)
  (hy : VectorMemQ y J) :
-- imply
  VectorMemQ (fun i => x i + y i) (vectorAdd I J) := by
-- proof
  apply StatMech.Exact3D.RatInterval.vectorAdd_memQ hx hy

/--
[vectorNeg_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma vectorNeg_memQ_eq
  {n : ℕ}
  {x : Fin n → ℚ}
  {I : IntervalVector n}
-- given
  (hx : VectorMemQ x I) :
-- imply
  VectorMemQ (fun i => -x i) (vectorNeg I) := by
-- proof
  apply StatMech.Exact3D.RatInterval.vectorNeg_memQ hx

/--
[vectorSub_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma vectorSub_memQ_eq
  {n : ℕ}
  {x y : Fin n → ℚ}
  {I J : IntervalVector n}
-- given
  (hx : VectorMemQ x I)
  (hy : VectorMemQ y J) :
-- imply
  VectorMemQ (fun i => x i - y i) (vectorSub I J) := by
-- proof
  apply StatMech.Exact3D.RatInterval.vectorSub_memQ hx hy

/--
[pointVector_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma pointVector_memQ_eq
  {n : ℕ}
  {x : Fin n → ℚ} :
-- imply
  VectorMemQ x (pointVector x) := by
-- proof
  apply StatMech.Exact3D.RatInterval.pointVector_memQ x

/--
[pointVector_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma pointVector_memR_eq
  {n : ℕ}
  {x : Fin n → ℚ} :
-- imply
  VectorMem (fun i => (x i : ℝ)) (pointVector x) := by
-- proof
  apply StatMech.Exact3D.RatInterval.pointVector_memR x

/--
[pointMatrix_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma pointMatrix_memQ_eq
  {m n : ℕ}
  {A : Fin m → Fin n → ℚ} :
-- imply
  MatrixMemQ A (pointMatrix A) := by
-- proof
  apply StatMech.Exact3D.RatInterval.pointMatrix_memQ A

/--
[pointMatrix_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma pointMatrix_memR_eq
  {m n : ℕ}
  {A : Fin m → Fin n → ℚ} :
-- imply
  MatrixMem (fun i j => (A i j : ℝ)) (pointMatrix A) := by
-- proof
  apply StatMech.Exact3D.RatInterval.pointMatrix_memR A

/--
[matrixVectorMul_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma matrixVectorMul_memR_eq
  {m n : ℕ}
  {A : Fin m → Fin n → ℝ}
  {x : Fin n → ℝ}
  {I : IntervalMatrix m n}
  {X : IntervalVector n}
-- given
  (hA : MatrixMem A I)
  (hx : VectorMem x X) :
-- imply
  VectorMem (fun i => ∑ j, A i j * x j) (matrixVectorMul I X) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorMul_memR hA hx

/--
[matrixVectorMulNonneg_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma matrixVectorMulNonneg_memR_eq
  {m n : ℕ}
  {A : Fin m → Fin n → ℝ}
  {x : Fin n → ℝ}
  {I : IntervalMatrix m n}
  {X : IntervalVector n}
-- given
  (hI : MatrixNonnegative I)
  (hX : VectorNonnegative X)
  (hA : MatrixMem A I)
  (hx : VectorMem x X) :
-- imply
  VectorMem (fun i => ∑ j, A i j * x j) (matrixVectorMulNonneg I X hI hX) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorMulNonneg_memR hI hX hA hx

/--
[matrixVectorResidual_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma matrixVectorResidual_memR_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {x : Fin n → ℝ}
  {I : IntervalMatrix n n}
  {X : IntervalVector n}
-- given
  (hA : MatrixMem A I)
  (hx : VectorMem x X) :
-- imply
  VectorMem (fun i => (∑ j, A i j * x j) - x i) (matrixVectorResidual I X) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorResidual_memR hA hx

/--
[matrixVectorResidualNonneg_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma matrixVectorResidualNonneg_memR_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {x : Fin n → ℝ}
  {I : IntervalMatrix n n}
  {X : IntervalVector n}
-- given
  (hI : MatrixNonnegative I)
  (hX : VectorNonnegative X)
  (hA : MatrixMem A I)
  (hx : VectorMem x X) :
-- imply
  VectorMem (fun i => (∑ j, A i j * x j) - x i) (matrixVectorResidualNonneg I X hI hX) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorResidualNonneg_memR hI hX hA hx

/--
[matrixVectorAffine_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma matrixVectorAffine_memR_eq
  {m n : ℕ}
  {A : Fin m → Fin n → ℝ}
  {b : Fin m → ℝ}
  {x : Fin n → ℝ}
  {I : IntervalMatrix m n}
  {B : IntervalVector m}
  {X : IntervalVector n}
-- given
  (hA : MatrixMem A I)
  (hb : VectorMem b B)
  (hx : VectorMem x X) :
-- imply
  VectorMem (fun i => (∑ j, A i j * x j) + b i) (matrixVectorAffine I B X) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorAffine_memR hA hb hx

/--
[matrixVectorAffineNonneg_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma matrixVectorAffineNonneg_memR_eq
  {m n : ℕ}
  {A : Fin m → Fin n → ℝ}
  {b : Fin m → ℝ}
  {x : Fin n → ℝ}
  {I : IntervalMatrix m n}
  {B : IntervalVector m}
  {X : IntervalVector n}
-- given
  (hI : MatrixNonnegative I)
  (hX : VectorNonnegative X)
  (hA : MatrixMem A I)
  (hb : VectorMem b B)
  (hx : VectorMem x X) :
-- imply
  VectorMem (fun i => (∑ j, A i j * x j) + b i) (matrixVectorAffineNonneg I B X hI hX) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorAffineNonneg_memR hI hX hA hb hx

/--
[matrixVectorAffineResidual_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma matrixVectorAffineResidual_memR_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {b x : Fin n → ℝ}
  {I : IntervalMatrix n n}
  {B X : IntervalVector n}
-- given
  (hA : MatrixMem A I)
  (hb : VectorMem b B)
  (hx : VectorMem x X) :
-- imply
  VectorMem (fun i => ((∑ j, A i j * x j) + b i) - x i) (matrixVectorAffineResidual I B X) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorAffineResidual_memR hA hb hx

/--
[matrixVectorAffineResidualNonneg_memR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma matrixVectorAffineResidualNonneg_memR_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {b x : Fin n → ℝ}
  {I : IntervalMatrix n n}
  {B X : IntervalVector n}
-- given
  (hI : MatrixNonnegative I)
  (hX : VectorNonnegative X)
  (hA : MatrixMem A I)
  (hb : VectorMem b B)
  (hx : VectorMem x X) :
-- imply
  VectorMem (fun i => ((∑ j, A i j * x j) + b i) - x i) (matrixVectorAffineResidualNonneg I B X hI hX) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorAffineResidualNonneg_memR hI hX hA hb hx

/--
[matrixVectorMulNonneg_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma matrixVectorMulNonneg_nonnegative_eq
  {m n : ℕ}
  {I : IntervalMatrix m n}
  {X : IntervalVector n}
-- given
  (hI : MatrixNonnegative I)
  (hX : VectorNonnegative X) :
-- imply
  VectorNonnegative (matrixVectorMulNonneg I X hI hX) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorMulNonneg_nonnegative hI hX

/--
[matrixVectorAffineNonneg_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma matrixVectorAffineNonneg_nonnegative_eq
  {m n : ℕ}
  {I : IntervalMatrix m n}
  {B : IntervalVector m}
  {X : IntervalVector n}
-- given
  (hI : MatrixNonnegative I)
  (hB : VectorNonnegative B)
  (hX : VectorNonnegative X) :
-- imply
  VectorNonnegative (matrixVectorAffineNonneg I B X hI hX) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorAffineNonneg_nonnegative hI hB hX

/--
[matrixVectorMul_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma matrixVectorMul_memQ_eq
  {m n : ℕ}
  {A : Fin m → Fin n → ℚ}
  {x : Fin n → ℚ}
  {I : IntervalMatrix m n}
  {X : IntervalVector n}
-- given
  (hA : MatrixMemQ A I)
  (hx : VectorMemQ x X) :
-- imply
  VectorMemQ (fun i => ∑ j, A i j * x j) (matrixVectorMul I X) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorMul_memQ hA hx

/--
[matrixVectorMulNonneg_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma matrixVectorMulNonneg_memQ_eq
  {m n : ℕ}
  {A : Fin m → Fin n → ℚ}
  {x : Fin n → ℚ}
  {I : IntervalMatrix m n}
  {X : IntervalVector n}
-- given
  (hI : MatrixNonnegative I)
  (hX : VectorNonnegative X)
  (hA : MatrixMemQ A I)
  (hx : VectorMemQ x X) :
-- imply
  VectorMemQ (fun i => ∑ j, A i j * x j) (matrixVectorMulNonneg I X hI hX) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorMulNonneg_memQ hI hX hA hx

/--
[matrixVectorResidual_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma matrixVectorResidual_memQ_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℚ}
  {x : Fin n → ℚ}
  {I : IntervalMatrix n n}
  {X : IntervalVector n}
-- given
  (hA : MatrixMemQ A I)
  (hx : VectorMemQ x X) :
-- imply
  VectorMemQ (fun i => (∑ j, A i j * x j) - x i) (matrixVectorResidual I X) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorResidual_memQ hA hx

/--
[matrixVectorResidualNonneg_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma matrixVectorResidualNonneg_memQ_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℚ}
  {x : Fin n → ℚ}
  {I : IntervalMatrix n n}
  {X : IntervalVector n}
-- given
  (hI : MatrixNonnegative I)
  (hX : VectorNonnegative X)
  (hA : MatrixMemQ A I)
  (hx : VectorMemQ x X) :
-- imply
  VectorMemQ (fun i => (∑ j, A i j * x j) - x i) (matrixVectorResidualNonneg I X hI hX) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorResidualNonneg_memQ hI hX hA hx

/--
[matrixVectorAffine_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma matrixVectorAffine_memQ_eq
  {m n : ℕ}
  {A : Fin m → Fin n → ℚ}
  {b : Fin m → ℚ}
  {x : Fin n → ℚ}
  {I : IntervalMatrix m n}
  {B : IntervalVector m}
  {X : IntervalVector n}
-- given
  (hA : MatrixMemQ A I)
  (hb : VectorMemQ b B)
  (hx : VectorMemQ x X) :
-- imply
  VectorMemQ (fun i => (∑ j, A i j * x j) + b i) (matrixVectorAffine I B X) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorAffine_memQ hA hb hx

/--
[matrixVectorAffineNonneg_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma matrixVectorAffineNonneg_memQ_eq
  {m n : ℕ}
  {A : Fin m → Fin n → ℚ}
  {b : Fin m → ℚ}
  {x : Fin n → ℚ}
  {I : IntervalMatrix m n}
  {B : IntervalVector m}
  {X : IntervalVector n}
-- given
  (hI : MatrixNonnegative I)
  (hX : VectorNonnegative X)
  (hA : MatrixMemQ A I)
  (hb : VectorMemQ b B)
  (hx : VectorMemQ x X) :
-- imply
  VectorMemQ (fun i => (∑ j, A i j * x j) + b i) (matrixVectorAffineNonneg I B X hI hX) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorAffineNonneg_memQ hI hX hA hb hx

/--
[matrixVectorAffineResidual_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma matrixVectorAffineResidual_memQ_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℚ}
  {b x : Fin n → ℚ}
  {I : IntervalMatrix n n}
  {B X : IntervalVector n}
-- given
  (hA : MatrixMemQ A I)
  (hb : VectorMemQ b B)
  (hx : VectorMemQ x X) :
-- imply
  VectorMemQ (fun i => ((∑ j, A i j * x j) + b i) - x i) (matrixVectorAffineResidual I B X) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorAffineResidual_memQ hA hb hx

/--
[matrixVectorAffineResidualNonneg_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean)
-/
@[path]
private lemma matrixVectorAffineResidualNonneg_memQ_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℚ}
  {b x : Fin n → ℚ}
  {I : IntervalMatrix n n}
  {B X : IntervalVector n}
-- given
  (hI : MatrixNonnegative I)
  (hX : VectorNonnegative X)
  (hA : MatrixMemQ A I)
  (hb : VectorMemQ b B)
  (hx : VectorMemQ x X) :
-- imply
  VectorMemQ (fun i => ((∑ j, A i j * x j) + b i) - x i) (matrixVectorAffineResidualNonneg I B X hI hX) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorAffineResidualNonneg_memQ hI hX hA hb hx


-- created on 2026-10-23

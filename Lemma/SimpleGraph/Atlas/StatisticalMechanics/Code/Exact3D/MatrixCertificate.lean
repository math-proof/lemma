import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.MatrixCertificate
open StatMech StatMech.Exact3D StatMech.Exact3D.RatInterval


/--
[abs_coord_le_supNormVec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma abs_coord_le_supNormVec_eq
  {n : ℕ}
  {x : Fin n → ℝ}
  {i : Fin n} :
-- imply
  |x i| ≤ supNormVec x := by
-- proof
  apply StatMech.Exact3D.RatInterval.abs_coord_le_supNormVec x i

/--
[supNormVec_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma supNormVec_nonneg_eq
  {n : ℕ}
  {x : Fin n → ℝ} :
-- imply
  0 ≤ supNormVec x := by
-- proof
  apply StatMech.Exact3D.RatInterval.supNormVec_nonneg x

/--
[matrixVectorMul_memR_matVec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma matrixVectorMul_memR_matVec_eq
  {m n : ℕ}
  {A : Fin m → Fin n → ℝ}
  {x : Fin n → ℝ}
  {I : IntervalMatrix m n}
  {X : IntervalVector n}
-- given
  (hA : MatrixMem A I)
  (hx : VectorMem x X) :
-- imply
  VectorMem (fun i => matVec A x i) (matrixVectorMul I X) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorMul_memR_matVec hA hx

/--
[matrixVectorMulNonneg_memR_matVec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma matrixVectorMulNonneg_memR_matVec_eq
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
  VectorMem (fun i => matVec A x i) (matrixVectorMulNonneg I X hI hX) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorMulNonneg_memR_matVec hI hX hA hx

/--
[matrixVectorResidual_memR_matVec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma matrixVectorResidual_memR_matVec_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {x : Fin n → ℝ}
  {I : IntervalMatrix n n}
  {X : IntervalVector n}
-- given
  (hA : MatrixMem A I)
  (hx : VectorMem x X) :
-- imply
  VectorMem (fun i => matVec A x i - x i) (matrixVectorResidual I X) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorResidual_memR_matVec hA hx

/--
[matrixVectorResidual_memR_matVec_pointVector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma matrixVectorResidual_memR_matVec_pointVector_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {I : IntervalMatrix n n}
  {center : Fin n → ℚ}
-- given
  (hA : MatrixMem A I) :
-- imply
  VectorMem (fun i => matVec A (fun j => (center j : ℝ)) i - (center i : ℝ)) (matrixVectorResidual I (pointVector center)) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorResidual_memR_matVec_pointVector hA center

/--
[matrixVectorResidualNonneg_memR_matVec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma matrixVectorResidualNonneg_memR_matVec_eq
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
  VectorMem (fun i => matVec A x i - x i) (matrixVectorResidualNonneg I X hI hX) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorResidualNonneg_memR_matVec hI hX hA hx

/--
[matrixVectorResidualNonneg_memR_matVec_pointVector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma matrixVectorResidualNonneg_memR_matVec_pointVector_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {I : IntervalMatrix n n}
  {center : Fin n → ℚ}
-- given
  (hI : MatrixNonnegative I)
  (hA : MatrixMem A I)
  (hcenter : ∀ i, 0 ≤ center i) :
-- imply
  VectorMem (fun i => matVec A (fun j => (center j : ℝ)) i - (center i : ℝ)) (matrixVectorResidualNonneg I (pointVector center) hI (pointVector_nonnegative hcenter)) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorResidualNonneg_memR_matVec_pointVector hI hA center hcenter

/--
[matrixVectorAffine_memR_affineMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma matrixVectorAffine_memR_affineMap_eq
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
  VectorMem (fun i => affineMap A b x i) (matrixVectorAffine I B X) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorAffine_memR_affineMap hA hb hx

/--
[matrixVectorAffineNonneg_memR_affineMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma matrixVectorAffineNonneg_memR_affineMap_eq
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
  VectorMem (fun i => affineMap A b x i) (matrixVectorAffineNonneg I B X hI hX) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorAffineNonneg_memR_affineMap hI hX hA hb hx

/--
[matrixVectorAffineResidual_memR_affineMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma matrixVectorAffineResidual_memR_affineMap_eq
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
  VectorMem (fun i => affineMap A b x i - x i) (matrixVectorAffineResidual I B X) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorAffineResidual_memR_affineMap hA hb hx

/--
[matrixVectorAffineResidual_memR_affineMap_pointVector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma matrixVectorAffineResidual_memR_affineMap_pointVector_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {b : Fin n → ℝ}
  {I : IntervalMatrix n n}
  {B : IntervalVector n}
  {center : Fin n → ℚ}
-- given
  (hA : MatrixMem A I)
  (hb : VectorMem b B) :
-- imply
  VectorMem (fun i => affineMap A b (fun j => (center j : ℝ)) i - (center i : ℝ)) (matrixVectorAffineResidual I B (pointVector center)) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorAffineResidual_memR_affineMap_pointVector hA hb center

/--
[matrixVectorAffineResidualNonneg_memR_affineMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma matrixVectorAffineResidualNonneg_memR_affineMap_eq
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
  VectorMem (fun i => affineMap A b x i - x i) (matrixVectorAffineResidualNonneg I B X hI hX) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorAffineResidualNonneg_memR_affineMap hI hX hA hb hx

/--
[matrixVectorAffineResidualNonneg_memR_affineMap_pointVector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma matrixVectorAffineResidualNonneg_memR_affineMap_pointVector_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {b : Fin n → ℝ}
  {I : IntervalMatrix n n}
  {B : IntervalVector n}
  {center : Fin n → ℚ}
-- given
  (hI : MatrixNonnegative I)
  (hA : MatrixMem A I)
  (hb : VectorMem b B)
  (hcenter : ∀ i, 0 ≤ center i) :
-- imply
  VectorMem (fun i => affineMap A b (fun j => (center j : ℝ)) i - (center i : ℝ)) (matrixVectorAffineResidualNonneg I B (pointVector center) hI (pointVector_nonnegative hcenter)) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorAffineResidualNonneg_memR_affineMap_pointVector hI hA hb center hcenter

/--
[matrixVectorAffine_memR_matVec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma matrixVectorAffine_memR_matVec_eq
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
  VectorMem (fun i => matVec A x i + b i) (matrixVectorAffine I B X) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorAffine_memR_matVec hA hb hx

/--
[matrixVectorAffineNonneg_memR_matVec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma matrixVectorAffineNonneg_memR_matVec_eq
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
  VectorMem (fun i => matVec A x i + b i) (matrixVectorAffineNonneg I B X hI hX) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorAffineNonneg_memR_matVec hI hX hA hb hx

/--
[matrixVectorAffineResidual_memR_matVec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma matrixVectorAffineResidual_memR_matVec_eq
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
  VectorMem (fun i => matVec A x i + b i - x i) (matrixVectorAffineResidual I B X) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorAffineResidual_memR_matVec hA hb hx

/--
[matrixVectorAffineResidualNonneg_memR_matVec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma matrixVectorAffineResidualNonneg_memR_matVec_eq
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
  VectorMem (fun i => matVec A x i + b i - x i) (matrixVectorAffineResidualNonneg I B X hI hX) := by
-- proof
  apply StatMech.Exact3D.RatInterval.matrixVectorAffineResidualNonneg_memR_matVec hI hX hA hb hx

/--
[IntervalOffDiagAbsRowSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma IntervalOffDiagAbsRowSum_nonneg_eq
  {n : ℕ}
  {I : IntervalMatrix n n}
  {i : Fin n} :
-- imply
  0 ≤ IntervalOffDiagAbsRowSum I i := by
-- proof
  apply StatMech.Exact3D.RatInterval.IntervalOffDiagAbsRowSum_nonneg I i

/--
[IntervalOffDiagAbsRowSum_nonneg_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma IntervalOffDiagAbsRowSum_nonneg_real_eq
  {n : ℕ}
  {I : IntervalMatrix n n}
  {i : Fin n} :
-- imply
  0 ≤ (IntervalOffDiagAbsRowSum I i : ℝ) := by
-- proof
  apply StatMech.Exact3D.RatInterval.IntervalOffDiagAbsRowSum_nonneg_real I i

/--
[matVec_eq_diag_add_offDiag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma matVec_eq_diag_add_offDiag_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {x : Fin n → ℝ}
  {i : Fin n} :
-- imply
  matVec A x i = A i i * x i + ∑ j, if j = i then 0 else A i j * x j := by
-- proof
  apply StatMech.Exact3D.RatInterval.matVec_eq_diag_add_offDiag A x i

/--
[offDiag_abs_matVec_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma offDiag_abs_matVec_bound_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {x : Fin n → ℝ}
  {i : Fin n}
-- given
  (hpivot : ∀ j, |x j| ≤ |x i|) :
-- imply
  |∑ j, if j = i then 0 else A i j * x j| ≤ offDiagAbsRowSum A i * |x i| := by
-- proof
  apply StatMech.Exact3D.RatInterval.offDiag_abs_matVec_bound A x i hpivot

/--
[gershgorin_row_bound_of_pivot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma gershgorin_row_bound_of_pivot_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {x : Fin n → ℝ}
  {lam : ℝ}
  {i : Fin n}
-- given
  (heig_i : matVec A x i = lam * x i)
  (hxi : x i ≠ 0)
  (hpivot : ∀ j, |x j| ≤ |x i|) :
-- imply
  |lam - A i i| ≤ offDiagAbsRowSum A i := by
-- proof
  apply StatMech.Exact3D.RatInterval.gershgorin_row_bound_of_pivot A x lam i heig_i hxi hpivot

/--
[offDiagAbsRowSum_le_interval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma offDiagAbsRowSum_le_interval_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {I : IntervalMatrix n n}
  {i : Fin n}
-- given
  (hA : MatrixMem A I) :
-- imply
  offDiagAbsRowSum A i ≤ (IntervalOffDiagAbsRowSum I i : ℝ) := by
-- proof
  apply StatMech.Exact3D.RatInterval.offDiagAbsRowSum_le_interval hA i

/--
[gershgorin_interval_row_bound_of_pivot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma gershgorin_interval_row_bound_of_pivot_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {I : IntervalMatrix n n}
  {x : Fin n → ℝ}
  {lam : ℝ}
  {i : Fin n}
-- given
  (hA : MatrixMem A I)
  (heig_i : matVec A x i = lam * x i)
  (hxi : x i ≠ 0)
  (hpivot : ∀ j, |x j| ≤ |x i|) :
-- imply
  |lam - A i i| ≤ (IntervalOffDiagAbsRowSum I i : ℝ) := by
-- proof
  apply StatMech.Exact3D.RatInterval.gershgorin_interval_row_bound_of_pivot hA x lam i heig_i hxi hpivot

/--
[exists_pivot_of_exists_nonzero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma exists_pivot_of_exists_nonzero_eq
  {n : ℕ}
  {x : Fin n → ℝ}
-- given
  (hnonzero : ∃ i, x i ≠ 0) :
-- imply
  ∃ i, x i ≠ 0 ∧ ∀ j, |x j| ≤ |x i| := by
-- proof
  apply StatMech.Exact3D.RatInterval.exists_pivot_of_exists_nonzero x hnonzero

/--
[gershgorin_bound_of_eigenvector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma gershgorin_bound_of_eigenvector_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {x : Fin n → ℝ}
  {lam : ℝ}
-- given
  (heig : ∀ i, matVec A x i = lam * x i)
  (hnonzero : ∃ i, x i ≠ 0) :
-- imply
  ∃ i, |lam - A i i| ≤ offDiagAbsRowSum A i := by
-- proof
  apply StatMech.Exact3D.RatInterval.gershgorin_bound_of_eigenvector A x lam heig hnonzero

/--
[gershgorin_interval_bound_of_eigenvector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma gershgorin_interval_bound_of_eigenvector_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {I : IntervalMatrix n n}
  {x : Fin n → ℝ}
  {lam : ℝ}
-- given
  (hA : MatrixMem A I)
  (heig : ∀ i, matVec A x i = lam * x i)
  (hnonzero : ∃ i, x i ≠ 0) :
-- imply
  ∃ i, |lam - A i i| ≤ (IntervalOffDiagAbsRowSum I i : ℝ) := by
-- proof
  apply StatMech.Exact3D.RatInterval.gershgorin_interval_bound_of_eigenvector hA x lam heig hnonzero

/--
[mem_intervalGershgorinRowInterval_of_rowDisk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma mem_intervalGershgorinRowInterval_of_rowDisk_eq
  {n : ℕ}
  {I : IntervalMatrix n n}
  {lam : ℝ}
  {i : Fin n}
-- given
  (hdisk : IntervalGershgorinRowDisk I lam i) :
-- imply
  (IntervalGershgorinRowInterval I i).MemR lam := by
-- proof
  apply StatMech.Exact3D.RatInterval.mem_intervalGershgorinRowInterval_of_rowDisk hdisk

/--
[intervalGershgorinRowDisk_of_pivot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma intervalGershgorinRowDisk_of_pivot_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {I : IntervalMatrix n n}
  {x : Fin n → ℝ}
  {lam : ℝ}
  {i : Fin n}
-- given
  (hA : MatrixMem A I)
  (heig_i : matVec A x i = lam * x i)
  (hxi : x i ≠ 0)
  (hpivot : ∀ j, |x j| ≤ |x i|) :
-- imply
  IntervalGershgorinRowDisk I lam i := by
-- proof
  apply StatMech.Exact3D.RatInterval.intervalGershgorinRowDisk_of_pivot hA x lam i heig_i hxi hpivot

/--
[exists_intervalGershgorinRowDisk_of_eigenvector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma exists_intervalGershgorinRowDisk_of_eigenvector_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {I : IntervalMatrix n n}
  {x : Fin n → ℝ}
  {lam : ℝ}
-- given
  (hA : MatrixMem A I)
  (heig : ∀ i, matVec A x i = lam * x i)
  (hnonzero : ∃ i, x i ≠ 0) :
-- imply
  ∃ i, IntervalGershgorinRowDisk I lam i := by
-- proof
  apply StatMech.Exact3D.RatInterval.exists_intervalGershgorinRowDisk_of_eigenvector hA x lam heig hnonzero

/--
[exists_mem_intervalGershgorinRowInterval_of_eigenvector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma exists_mem_intervalGershgorinRowInterval_of_eigenvector_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {I : IntervalMatrix n n}
  {x : Fin n → ℝ}
  {lam : ℝ}
-- given
  (hA : MatrixMem A I)
  (heig : ∀ i, matVec A x i = lam * x i)
  (hnonzero : ∃ i, x i ≠ 0) :
-- imply
  ∃ i, (IntervalGershgorinRowInterval I i).MemR lam := by
-- proof
  apply StatMech.Exact3D.RatInterval.exists_mem_intervalGershgorinRowInterval_of_eigenvector hA x lam heig hnonzero

/--
[intervalGershgorinRowExcludes_of_endpointSeparated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma intervalGershgorinRowExcludes_of_endpointSeparated_eq
  {n : ℕ}
  {I : IntervalMatrix n n}
  {lam : ℝ}
  {i : Fin n}
-- given
  (hsep : IntervalGershgorinRowEndpointSeparated I lam i) :
-- imply
  IntervalGershgorinRowExcludes I lam i := by
-- proof
  apply StatMech.Exact3D.RatInterval.intervalGershgorinRowExcludes_of_endpointSeparated hsep

/--
[intervalGershgorinRowEndpointSeparated_of_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma intervalGershgorinRowEndpointSeparated_of_mem_Icc_eq
  {n : ℕ}
  {I : IntervalMatrix n n}
  {lo hi lam : ℝ}
  {i : Fin n}
-- given
  (hsep : IntervalGershgorinRowEndpointSeparatedOnIcc I lo hi i)
  (hlam : lam ∈ Set.Icc lo hi) :
-- imply
  IntervalGershgorinRowEndpointSeparated I lam i := by
-- proof
  apply StatMech.Exact3D.RatInterval.intervalGershgorinRowEndpointSeparated_of_mem_Icc hsep hlam

/--
[no_eigenvector_of_gershgorin_exclusion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma no_eigenvector_of_gershgorin_exclusion_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {lam : ℝ}
  {x : Fin n → ℝ}
-- given
  (hexcl : ∀ i, GershgorinRowExcludes A lam i)
  (heig : ∀ i, matVec A x i = lam * x i)
  (hnonzero : ∃ i, x i ≠ 0) :
-- imply
  False := by
-- proof
  apply StatMech.Exact3D.RatInterval.no_eigenvector_of_gershgorin_exclusion A lam hexcl x heig hnonzero

/--
[not_exists_eigenvector_of_gershgorin_exclusion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma not_exists_eigenvector_of_gershgorin_exclusion_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {lam : ℝ}
-- given
  (hexcl : ∀ i, GershgorinRowExcludes A lam i) :
-- imply
  ¬ ∃ x : Fin n → ℝ, (∀ i, matVec A x i = lam * x i) ∧ ∃ i, x i ≠ 0 := by
-- proof
  apply StatMech.Exact3D.RatInterval.not_exists_eigenvector_of_gershgorin_exclusion A lam hexcl

/--
[no_eigenvector_of_interval_gershgorin_exclusion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma no_eigenvector_of_interval_gershgorin_exclusion_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {I : IntervalMatrix n n}
  {lam : ℝ}
  {x : Fin n → ℝ}
-- given
  (hA : MatrixMem A I)
  (hexcl : ∀ i, IntervalGershgorinRowExcludes I lam i)
  (heig : ∀ i, matVec A x i = lam * x i)
  (hnonzero : ∃ i, x i ≠ 0) :
-- imply
  False := by
-- proof
  apply StatMech.Exact3D.RatInterval.no_eigenvector_of_interval_gershgorin_exclusion hA lam hexcl x heig hnonzero

/--
[not_exists_eigenvector_of_interval_gershgorin_exclusion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma not_exists_eigenvector_of_interval_gershgorin_exclusion_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {I : IntervalMatrix n n}
  {lam : ℝ}
-- given
  (hA : MatrixMem A I)
  (hexcl : ∀ i, IntervalGershgorinRowExcludes I lam i) :
-- imply
  ¬ ∃ x : Fin n → ℝ, (∀ i, matVec A x i = lam * x i) ∧ ∃ i, x i ≠ 0 := by
-- proof
  apply StatMech.Exact3D.RatInterval.not_exists_eigenvector_of_interval_gershgorin_exclusion hA lam hexcl

/--
[no_eigenvector_of_interval_gershgorin_endpoint_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma no_eigenvector_of_interval_gershgorin_endpoint_separation_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {I : IntervalMatrix n n}
  {lam : ℝ}
  {x : Fin n → ℝ}
-- given
  (hA : MatrixMem A I)
  (hsep : ∀ i, IntervalGershgorinRowEndpointSeparated I lam i)
  (heig : ∀ i, matVec A x i = lam * x i)
  (hnonzero : ∃ i, x i ≠ 0) :
-- imply
  False := by
-- proof
  apply StatMech.Exact3D.RatInterval.no_eigenvector_of_interval_gershgorin_endpoint_separation hA lam hsep x heig hnonzero

/--
[not_exists_eigenvector_of_interval_gershgorin_endpoint_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma not_exists_eigenvector_of_interval_gershgorin_endpoint_separation_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {I : IntervalMatrix n n}
  {lam : ℝ}
-- given
  (hA : MatrixMem A I)
  (hsep : ∀ i, IntervalGershgorinRowEndpointSeparated I lam i) :
-- imply
  ¬ ∃ x : Fin n → ℝ, (∀ i, matVec A x i = lam * x i) ∧ ∃ i, x i ≠ 0 := by
-- proof
  apply StatMech.Exact3D.RatInterval.not_exists_eigenvector_of_interval_gershgorin_endpoint_separation hA lam hsep

/--
[no_eigenvector_with_eigenvalue_in_Icc_of_interval_gershgorin_endpoint_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma no_eigenvector_with_eigenvalue_in_Icc_of_interval_gershgorin_endpoint_separation_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {I : IntervalMatrix n n}
  {lo hi lam : ℝ}
  {x : Fin n → ℝ}
-- given
  (hA : MatrixMem A I)
  (hlam : lam ∈ Set.Icc lo hi)
  (hsep : ∀ i, IntervalGershgorinRowEndpointSeparatedOnIcc I lo hi i)
  (heig : ∀ i, matVec A x i = lam * x i)
  (hnonzero : ∃ i, x i ≠ 0) :
-- imply
  False := by
-- proof
  apply StatMech.Exact3D.RatInterval.no_eigenvector_with_eigenvalue_in_Icc_of_interval_gershgorin_endpoint_separation hA hlam hsep x heig hnonzero

/--
[not_exists_eigenvector_with_eigenvalue_in_Icc_of_interval_gershgorin_endpoint_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma not_exists_eigenvector_with_eigenvalue_in_Icc_of_interval_gershgorin_endpoint_separation_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {I : IntervalMatrix n n}
-- given
  (hA : MatrixMem A I)
  (lo hi : ℝ)
  (hsep : ∀ i, IntervalGershgorinRowEndpointSeparatedOnIcc I lo hi i) :
-- imply
  ¬ ∃ lam : ℝ, lam ∈ Set.Icc lo hi ∧ ∃ x : Fin n → ℝ, (∀ i, matVec A x i = lam * x i) ∧ ∃ i, x i ≠ 0 := by
-- proof
  apply StatMech.Exact3D.RatInterval.not_exists_eigenvector_with_eigenvalue_in_Icc_of_interval_gershgorin_endpoint_separation hA lo hi hsep

/--
[not_exists_eigenvector_in_Icc_of_endpoint_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma not_exists_eigenvector_in_Icc_of_endpoint_separation_eq
  {n : ℕ}
  {A : Fin n → Fin n → ℝ}
  {I : IntervalMatrix n n}
-- given
  (hA : MatrixMem A I)
  (lo hi : ℝ)
  (hsep : ∀ i, IntervalGershgorinRowEndpointSeparatedOnIcc I lo hi i) :
-- imply
  ¬ ∃ lam : ℝ, lam ∈ Set.Icc lo hi ∧ ∃ x : Fin n → ℝ, (∀ i, matVec A x i = lam * x i) ∧ ∃ i, x i ≠ 0 := by
-- proof
  apply StatMech.Exact3D.RatInterval.not_exists_eigenvector_in_Icc_of_endpoint_separation hA lo hi hsep

/--
[RowSumContraction.apply_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma apply_bound_eq
  {n : ℕ}
  {I : IntervalMatrix n n}
  {A : Fin n → Fin n → ℝ}
  {x : Fin n → ℝ}
  {i : Fin n}
-- given
  (hI : RowSumContraction I)
  (hA : MatrixMem A I) :
-- imply
  |matVec A x i| ≤ (hI.c : ℝ) * supNormVec x := by
-- proof
  apply StatMech.Exact3D.RatInterval.RowSumContraction.apply_bound hI hA x i

/--
[RowSumContraction.constant_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma constant_lt_one_eq
  {n : ℕ}
  {I : IntervalMatrix n n}
-- given
  (hI : RowSumContraction I) :
-- imply
  (hI.c : ℝ) < 1 := by
-- proof
  apply StatMech.Exact3D.RatInterval.RowSumContraction.constant_lt_one hI

/--
[ColumnSumContraction.apply_l1_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma apply_l1_bound_eq
  {n : ℕ}
  {I : IntervalMatrix n n}
  {A : Fin n → Fin n → ℝ}
  {x : Fin n → ℝ}
-- given
  (hI : ColumnSumContraction I)
  (hA : MatrixMem A I) :
-- imply
  supNormVec (fun i => matVec A x i) ≤ (hI.c : ℝ) * supNormVec x := by
-- proof
  apply StatMech.Exact3D.RatInterval.ColumnSumContraction.apply_l1_bound hI hA x

/--
[ColumnSumContraction.constant_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean)
-/
@[path]
private lemma constant_lt_one_eq_2
  {n : ℕ}
  {I : IntervalMatrix n n}
-- given
  (hI : ColumnSumContraction I) :
-- imply
  (hI.c : ℝ) < 1 := by
-- proof
  apply StatMech.Exact3D.RatInterval.ColumnSumContraction.constant_lt_one hI


-- created on 2026-10-23

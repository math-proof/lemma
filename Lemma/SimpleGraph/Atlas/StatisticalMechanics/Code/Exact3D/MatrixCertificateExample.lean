import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificateExample.Part4
open StatMech StatMech.Exact3D StatMech.Exact3D.MatrixCertificateExample


/--
[stableIntervals_eq_pointMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stableIntervals_eq_pointMatrix_eq :
-- imply
  stableIntervals = RatInterval.pointMatrix stableMatrixQ := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stableIntervals_eq_pointMatrix

/--
[stableMatrix_eq_rational](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stableMatrix_eq_rational_eq :
-- imply
  stableMatrix = fun i j => (stableMatrixQ i j : ℝ) := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stableMatrix_eq_rational

/--
[stableMatrix_mem_intervals](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stableMatrix_mem_intervals_eq :
-- imply
  RatInterval.MatrixMem stableMatrix stableIntervals := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stableMatrix_mem_intervals

/--
[stableMatrix_mem_pointMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stableMatrix_mem_pointMatrix_eq :
-- imply
  RatInterval.MatrixMem stableMatrix (RatInterval.pointMatrix stableMatrixQ) := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stableMatrix_mem_pointMatrix

/--
[stableRationalResidual_memQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stableRationalResidual_memQ_eq :
-- imply
  RatInterval.VectorMemQ (fun i => (∑ j, stableMatrixQ i j * stableCenterQ j) - stableCenterQ i) (RatInterval.matrixVectorResidual (RatInterval.pointMatrix stableMatrixQ) (RatInterval.pointVector stableCenterQ)) := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stableRationalResidual_memQ

/--
[stableRationalResidual_absSum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stableRationalResidual_absSum_zero_eq :
-- imply
  RatInterval.VectorAbsSum (RatInterval.matrixVectorResidual (RatInterval.pointMatrix stableMatrixQ) (RatInterval.pointVector stableCenterQ)) = 0 := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stableRationalResidual_absSum_zero

/--
[stableMatrix_map_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stableMatrix_map_zero_eq :
-- imply
  (fun i => RatInterval.matVec stableMatrix (0 : Fin 2 → ℝ) i) = 0 := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stableMatrix_map_zero

/--
[stableColumnClosedBallCertificate_exists_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stableColumnClosedBallCertificate_exists_fixedPoint_eq :
-- imply
  ∃ p : Fin 2 → ℝ, (fun x i => RatInterval.matVec stableMatrix x i) p = p ∧ FiniteContraction.ClosedBall stableColumnClosedBallCertificate.center stableColumnClosedBallCertificate.radius p := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stableColumnClosedBallCertificate_exists_fixedPoint

/--
[stableColumnClosedBallCertificate_fixedPoint_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stableColumnClosedBallCertificate_fixedPoint_eq_zero_eq :
-- imply
  stableColumnClosedBallCertificate.fixedPoint = 0 := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stableColumnClosedBallCertificate_fixedPoint_eq_zero

/--
[stableMatrix_apply_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stableMatrix_apply_bound_eq
  {x : Fin 2 → ℝ}
  {i : Fin 2} :
-- imply
  |RatInterval.matVec stableMatrix x i| ≤ ((1 / 2 : ℚ) : ℝ) * RatInterval.supNormVec x := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stableMatrix_apply_bound x i

/--
[stablePointMatrix_apply_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stablePointMatrix_apply_bound_eq
  {x : Fin 2 → ℝ}
  {i : Fin 2} :
-- imply
  |RatInterval.matVec stableMatrix x i| ≤ ((1 / 2 : ℚ) : ℝ) * RatInterval.supNormVec x := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stablePointMatrix_apply_bound x i

/--
[stableMatrix_apply_l1_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stableMatrix_apply_l1_bound_eq
  {x : Fin 2 → ℝ} :
-- imply
  RatInterval.supNormVec (fun i => RatInterval.matVec stableMatrix x i) ≤ ((1 / 2 : ℚ) : ℝ) * RatInterval.supNormVec x := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stableMatrix_apply_l1_bound x

/--
[stablePointMatrix_apply_l1_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stablePointMatrix_apply_l1_bound_eq
  {x : Fin 2 → ℝ} :
-- imply
  RatInterval.supNormVec (fun i => RatInterval.matVec stableMatrix x i) ≤ ((1 / 2 : ℚ) : ℝ) * RatInterval.supNormVec x := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stablePointMatrix_apply_l1_bound x

/--
[stableIntervals_offDiagAbsRowSum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stableIntervals_offDiagAbsRowSum_zero_eq
  {i : Fin 2} :
-- imply
  RatInterval.IntervalOffDiagAbsRowSum stableIntervals i = 0 := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stableIntervals_offDiagAbsRowSum_zero i

/--
[stableMatrix_gershgorin_zero_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stableMatrix_gershgorin_zero_radius_eq
  {x : Fin 2 → ℝ}
  {lam : ℝ}
  {i : Fin 2}
-- given
  (heig_i : RatInterval.matVec stableMatrix x i = lam * x i)
  (hxi : x i ≠ 0)
  (hpivot : ∀ j, |x j| ≤ |x i|) :
-- imply
  |lam - stableMatrix i i| ≤ 0 := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stableMatrix_gershgorin_zero_radius x lam i heig_i hxi hpivot

/--
[stableMatrix_eigenvalue_gershgorin_zero_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stableMatrix_eigenvalue_gershgorin_zero_radius_eq
  {x : Fin 2 → ℝ}
  {lam : ℝ}
-- given
  (heig : ∀ i, RatInterval.matVec stableMatrix x i = lam * x i)
  (hnonzero : ∃ i, x i ≠ 0) :
-- imply
  ∃ i, |lam - stableMatrix i i| ≤ 0 := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stableMatrix_eigenvalue_gershgorin_zero_radius x lam heig hnonzero

/--
[stableMatrix_eigenvalue_mem_interval_gershgorin_disk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stableMatrix_eigenvalue_mem_interval_gershgorin_disk_eq
  {x : Fin 2 → ℝ}
  {lam : ℝ}
-- given
  (heig : ∀ i, RatInterval.matVec stableMatrix x i = lam * x i)
  (hnonzero : ∃ i, x i ≠ 0) :
-- imply
  ∃ i, RatInterval.IntervalGershgorinRowDisk stableIntervals lam i := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stableMatrix_eigenvalue_mem_interval_gershgorin_disk x lam heig hnonzero

/--
[stableMatrix_eigenvalue_mem_interval_gershgorin_rowInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stableMatrix_eigenvalue_mem_interval_gershgorin_rowInterval_eq
  {x : Fin 2 → ℝ}
  {lam : ℝ}
-- given
  (heig : ∀ i, RatInterval.matVec stableMatrix x i = lam * x i)
  (hnonzero : ∃ i, x i ≠ 0) :
-- imply
  ∃ i, (RatInterval.IntervalGershgorinRowInterval stableIntervals i).MemR lam := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stableMatrix_eigenvalue_mem_interval_gershgorin_rowInterval x lam heig hnonzero

/--
[stableMatrix_eigenvalue_eq_half_or_third](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stableMatrix_eigenvalue_eq_half_or_third_eq
  {x : Fin 2 → ℝ}
  {lam : ℝ}
-- given
  (heig : ∀ i, RatInterval.matVec stableMatrix x i = lam * x i)
  (hnonzero : ∃ i, x i ≠ 0) :
-- imply
  lam = (1 : ℝ) / 2 ∨ lam = (1 : ℝ) / 3 := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stableMatrix_eigenvalue_eq_half_or_third x lam heig hnonzero

/--
[stableIntervals_endpointSeparated_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stableIntervals_endpointSeparated_zero_eq
  {i : Fin 2} :
-- imply
  RatInterval.IntervalGershgorinRowEndpointSeparated stableIntervals 0 i := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stableIntervals_endpointSeparated_zero i

/--
[stableMatrix_not_exists_zero_eigenvector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stableMatrix_not_exists_zero_eigenvector_eq :
-- imply
  ¬ ∃ x : Fin 2 → ℝ, (∀ i, RatInterval.matVec stableMatrix x i = 0 * x i) ∧ ∃ i, x i ≠ 0 := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stableMatrix_not_exists_zero_eigenvector

/--
[stableIntervals_endpointSeparatedOnIcc_near_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stableIntervals_endpointSeparatedOnIcc_near_zero_eq
  {i : Fin 2} :
-- imply
  RatInterval.IntervalGershgorinRowEndpointSeparatedOnIcc stableIntervals (-(1 : ℝ) / 10) ((1 : ℝ) / 10) i := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stableIntervals_endpointSeparatedOnIcc_near_zero i

/--
[stableMatrix_not_exists_eigenvector_with_eigenvalue_near_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean)
-/
@[path]
private lemma stableMatrix_not_exists_eigenvector_with_eigenvalue_near_zero_eq :
-- imply
  ¬ ∃ lam : ℝ, lam ∈ Set.Icc (-(1 : ℝ) / 10) ((1 : ℝ) / 10) ∧ ∃ x : Fin 2 → ℝ, (∀ i, RatInterval.matVec stableMatrix x i = lam * x i) ∧ ∃ i, x i ≠ 0 := by
-- proof
  apply StatMech.Exact3D.MatrixCertificateExample.stableMatrix_not_exists_eigenvector_with_eigenvalue_near_zero


-- created on 2026-10-23

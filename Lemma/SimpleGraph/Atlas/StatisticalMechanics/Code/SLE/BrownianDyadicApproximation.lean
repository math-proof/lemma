import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.SLE.BrownianDyadicApproximation.Part2
open Filter MeasureTheory ProbabilityTheory Set StatMech StatMech.SLE


/--
[brownianDyadicDenominator_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean)
-/
@[path]
private lemma brownianDyadicDenominator_succ_eq
  {n : Nat} :
-- imply
  brownianDyadicDenominator (n + 1) = brownianDyadicDenominator n * 256 := by
-- proof
  apply StatMech.SLE.brownianDyadicDenominator_succ n

/--
[brownianDyadicApproxIndex_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean)
-/
@[path]
private lemma brownianDyadicApproxIndex_le_eq
  {N n : Nat}
  {t : Real}
-- given
  (htLower : -(N : Real) <= t)
  (htUpper : t <= N) :
-- imply
  brownianDyadicApproxIndex N n t <= 2 * N * brownianDyadicDenominator n := by
-- proof
  apply StatMech.SLE.brownianDyadicApproxIndex_le N n htLower htUpper

/--
[brownianDyadicApproxPoint_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean)
-/
@[path]
private lemma brownianDyadicApproxPoint_le_eq
  {N n : Nat}
  {t : Real}
-- given
  (htLower : -(N : Real) <= t) :
-- imply
  brownianDyadicApproxPoint N n t <= t := by
-- proof
  apply StatMech.SLE.brownianDyadicApproxPoint_le N n htLower

/--
[brownianDyadicApproxPoint_lt_add_mesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean)
-/
@[path]
private lemma brownianDyadicApproxPoint_lt_add_mesh_eq
  {N n : Nat}
  {t : Real}
-- given
  (htLower : -(N : Real) <= t) :
-- imply
  t < brownianDyadicApproxPoint N n t + ((brownianDyadicDenominator n : Nat) : Real)⁻¹ := by
-- proof
  apply StatMech.SLE.brownianDyadicApproxPoint_lt_add_mesh N n htLower

/--
[dist_brownianDyadicApproxPoint_lt_mesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean)
-/
@[path]
private lemma dist_brownianDyadicApproxPoint_lt_mesh_eq
  {N n : Nat}
  {t : Real}
-- given
  (htLower : -(N : Real) <= t) :
-- imply
  dist (brownianDyadicApproxPoint N n t) t < ((brownianDyadicDenominator n : Nat) : Real)⁻¹ := by
-- proof
  apply StatMech.SLE.dist_brownianDyadicApproxPoint_lt_mesh N n htLower

/--
[brownianDyadicApproxIndex_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean)
-/
@[path]
private lemma brownianDyadicApproxIndex_mono_eq
  {N n : Nat}
  {s t : Real}
-- given
  (hst : s <= t) :
-- imply
  brownianDyadicApproxIndex N n s <= brownianDyadicApproxIndex N n t := by
-- proof
  apply StatMech.SLE.brownianDyadicApproxIndex_mono N n hst

/--
[brownianDyadicApproxIndex_lt_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean)
-/
@[path]
private lemma brownianDyadicApproxIndex_lt_add_two_eq
  {N n : Nat}
  {s t : Real}
-- given
  (hsLower : -(N : Real) <= s)
  (hst : s <= t)
  (hclose : t - s < ((brownianDyadicDenominator n : Nat) : Real)⁻¹) :
-- imply
  brownianDyadicApproxIndex N n t < brownianDyadicApproxIndex N n s + 2 := by
-- proof
  apply StatMech.SLE.brownianDyadicApproxIndex_lt_add_two N n hsLower hst hclose

/--
[brownianDyadicApproxIndex_mul_le_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean)
-/
@[path]
private lemma brownianDyadicApproxIndex_mul_le_succ_eq
  {N n : Nat}
  {t : Real}
-- given
  (htLower : -(N : Real) <= t) :
-- imply
  brownianDyadicApproxIndex N n t * 256 <= brownianDyadicApproxIndex N (n + 1) t := by
-- proof
  apply StatMech.SLE.brownianDyadicApproxIndex_mul_le_succ N n htLower

/--
[brownianDyadicApproxIndex_succ_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean)
-/
@[path]
private lemma brownianDyadicApproxIndex_succ_lt_eq
  {N n : Nat}
  {t : Real}
-- given
  (htLower : -(N : Real) <= t) :
-- imply
  brownianDyadicApproxIndex N (n + 1) t < (brownianDyadicApproxIndex N n t + 1) * 256 := by
-- proof
  apply StatMech.SLE.brownianDyadicApproxIndex_succ_lt N n htLower

/--
[brownianDyadicPoint_succ_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean)
-/
@[path]
private lemma brownianDyadicPoint_succ_mul_eq
  {N n k : Nat} :
-- imply
  brownianDyadicPoint N (n + 1) (k * 256) = brownianDyadicPoint N n k := by
-- proof
  apply StatMech.SLE.brownianDyadicPoint_succ_mul N n k

/--
[edist_brownianCoordinateProcess_approxPoint_succ_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean)
-/
@[path]
private lemma edist_brownianCoordinateProcess_approxPoint_succ_le_eq
  {N n : Nat}
  {t : Real}
-- given
  (omega : Real -> Real)
  (htLower : -(N : Real) <= t)
  (htUpper : t <= N)
  (hedge : ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator (n + 1)), edist (brownianCoordinateProcess (brownianDyadicPoint N (n + 1) k) omega) (brownianCoordinateProcess (brownianDyadicPoint N (n + 1) (k + 1)) omega) < brownianDyadicThreshold (n + 1)) :
-- imply
  edist (brownianCoordinateProcess (brownianDyadicApproxPoint N n t) omega) (brownianCoordinateProcess (brownianDyadicApproxPoint N (n + 1) t) omega) <= (256 : ENNReal) * brownianDyadicThreshold (n + 1) := by
-- proof
  apply StatMech.SLE.edist_brownianCoordinateProcess_approxPoint_succ_le omega N n htLower htUpper hedge

/--
[edist_brownianCoordinateProcess_approxPoint_le_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean)
-/
@[path]
private lemma edist_brownianCoordinateProcess_approxPoint_le_of_le_eq
  {N n : Nat}
  {s t : Real}
-- given
  (omega : Real -> Real)
  (hsLower : -(N : Real) <= s)
  (htUpper : t <= N)
  (hst : s <= t)
  (hclose : t - s < ((brownianDyadicDenominator n : Nat) : Real)⁻¹)
  (hedge : ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator n), edist (brownianCoordinateProcess (brownianDyadicPoint N n k) omega) (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega) < brownianDyadicThreshold n) :
-- imply
  edist (brownianCoordinateProcess (brownianDyadicApproxPoint N n s) omega) (brownianCoordinateProcess (brownianDyadicApproxPoint N n t) omega) <= brownianDyadicThreshold n := by
-- proof
  apply StatMech.SLE.edist_brownianCoordinateProcess_approxPoint_le_of_le omega N n hsLower htUpper hst hclose hedge

/--
[edist_brownianCoordinateProcess_approxPoint_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean)
-/
@[path]
private lemma edist_brownianCoordinateProcess_approxPoint_le_eq
  {N n : Nat}
  {s t : Real}
-- given
  (omega : Real -> Real)
  (hsLower : -(N : Real) <= s)
  (hsUpper : s <= N)
  (htLower : -(N : Real) <= t)
  (htUpper : t <= N)
  (hclose : dist s t < ((brownianDyadicDenominator n : Nat) : Real)⁻¹)
  (hedge : ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator n), edist (brownianCoordinateProcess (brownianDyadicPoint N n k) omega) (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega) < brownianDyadicThreshold n) :
-- imply
  edist (brownianCoordinateProcess (brownianDyadicApproxPoint N n s) omega) (brownianCoordinateProcess (brownianDyadicApproxPoint N n t) omega) <= brownianDyadicThreshold n := by
-- proof
  apply StatMech.SLE.edist_brownianCoordinateProcess_approxPoint_le omega N n hsLower hsUpper htLower htUpper hclose hedge

/--
[cauchySeq_brownianCoordinateProcess_brownianDyadicApproxPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean)
-/
@[path]
private lemma cauchySeq_brownianCoordinateProcess_brownianDyadicApproxPoint_eq
  {N : Nat}
  {t : Real}
-- given
  (omega : Real -> Real)
  (htLower : -(N : Real) <= t)
  (htUpper : t <= N)
  (hgood : ∀ᶠ n in atTop, ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator n), edist (brownianCoordinateProcess (brownianDyadicPoint N n k) omega) (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega) < brownianDyadicThreshold n) :
-- imply
  CauchySeq (fun n => brownianCoordinateProcess (brownianDyadicApproxPoint N n t) omega) := by
-- proof
  apply StatMech.SLE.cauchySeq_brownianCoordinateProcess_brownianDyadicApproxPoint omega N htLower htUpper hgood

/--
[tendsto_brownianCoordinateProcess_brownianDyadicApproxPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean)
-/
@[path]
private lemma tendsto_brownianCoordinateProcess_brownianDyadicApproxPoint_eq
  {N : Nat}
  {t : Real}
-- given
  (omega : Real -> Real)
  (htLower : -(N : Real) <= t)
  (htUpper : t <= N)
  (hgood : ∀ᶠ n in atTop, ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator n), edist (brownianCoordinateProcess (brownianDyadicPoint N n k) omega) (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega) < brownianDyadicThreshold n) :
-- imply
  Tendsto (fun n => brownianCoordinateProcess (brownianDyadicApproxPoint N n t) omega) atTop (nhds (brownianDyadicLimit N t omega)) := by
-- proof
  apply StatMech.SLE.tendsto_brownianCoordinateProcess_brownianDyadicApproxPoint omega N htLower htUpper hgood

/--
[edist_brownianCoordinateProcess_approxPoint_limit_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean)
-/
@[path]
private lemma edist_brownianCoordinateProcess_approxPoint_limit_le_eq
  {N n : Nat}
  {t : Real}
-- given
  (omega : Real -> Real)
  (htLower : -(N : Real) <= t)
  (htUpper : t <= N)
  (hgoodFrom : ∀ m, n <= m -> ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator m), edist (brownianCoordinateProcess (brownianDyadicPoint N m k) omega) (brownianCoordinateProcess (brownianDyadicPoint N m (k + 1)) omega) < brownianDyadicThreshold m) :
-- imply
  edist (brownianCoordinateProcess (brownianDyadicApproxPoint N n t) omega) (brownianDyadicLimit N t omega) <= (256 : ENNReal) * brownianDyadicThreshold n := by
-- proof
  apply StatMech.SLE.edist_brownianCoordinateProcess_approxPoint_limit_le omega N n htLower htUpper hgoodFrom

/--
[edist_brownianDyadicLimit_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean)
-/
@[path]
private lemma edist_brownianDyadicLimit_le_eq
  {N n : Nat}
  {s t : Real}
-- given
  (omega : Real -> Real)
  (hsLower : -(N : Real) <= s)
  (hsUpper : s <= N)
  (htLower : -(N : Real) <= t)
  (htUpper : t <= N)
  (hclose : dist s t < ((brownianDyadicDenominator n : Nat) : Real)⁻¹)
  (hgoodFrom : ∀ m, n <= m -> ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator m), edist (brownianCoordinateProcess (brownianDyadicPoint N m k) omega) (brownianCoordinateProcess (brownianDyadicPoint N m (k + 1)) omega) < brownianDyadicThreshold m) :
-- imply
  edist (brownianDyadicLimit N s omega) (brownianDyadicLimit N t omega) <= (513 : ENNReal) * brownianDyadicThreshold n := by
-- proof
  apply StatMech.SLE.edist_brownianDyadicLimit_le omega N n hsLower hsUpper htLower htUpper hclose hgoodFrom

/--
[continuousOn_brownianDyadicLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean)
-/
@[path]
private lemma continuousOn_brownianDyadicLimit_eq
  {N : Nat}
-- given
  (omega : Real -> Real)
  (hgood : ∀ᶠ n in atTop, ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator n), edist (brownianCoordinateProcess (brownianDyadicPoint N n k) omega) (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega) < brownianDyadicThreshold n) :
-- imply
  ContinuousOn (fun t => brownianDyadicLimit N t omega) (Set.Icc (-(N : Real)) N) := by
-- proof
  apply StatMech.SLE.continuousOn_brownianDyadicLimit omega N hgood


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.SmoothCurveDivisors.Part2
open IsDedekindDomain SmoothCurveDivisors


namespace SmoothCurveDivisors

/--
[weilDivisor_sum_of_points_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothCurveDivisors.lean)
-/
@[path]
lemma weilDivisor_sum_of_points_injective
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K] :
-- imply
  Function.Injective (weilDivisor_sum_of_points R K) :=
-- proof
  (weilDivisor_sum_of_points_equiv R K).injective

end SmoothCurveDivisors

namespace SmoothCurveDivisors

/--
[weilDivisor_sum_of_points_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothCurveDivisors.lean)
-/
@[path]
lemma weilDivisor_sum_of_points_surjective
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K] :
-- imply
  Function.Surjective (weilDivisor_sum_of_points R K) :=
-- proof
  (weilDivisor_sum_of_points_equiv R K).surjective

end SmoothCurveDivisors

/--
[eq_of_count_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothCurveDivisors.lean)
-/
@[path]
private lemma eq_of_count_eq_eq
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {I J : FractionalIdeal (nonZeroDivisors R) K}
-- given
  (hI : I ≠ 0)
  (hJ : J ≠ 0)
  (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
-- imply
  I = J := by
-- proof
  apply SmoothCurveDivisors.eq_of_count_eq R K hI hJ h

/--
[bwd_fwd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothCurveDivisors.lean)
-/
@[path]
private lemma bwd_fwd_eq
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {I : (FractionalIdeal (nonZeroDivisors R) K)ˣ} :
-- imply
  bwdFun R K (fwdFun R K I) = I := by
-- proof
  apply SmoothCurveDivisors.bwd_fwd R K I

/--
[fwd_bwd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothCurveDivisors.lean)
-/
@[path]
private lemma fwd_bwd_eq
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {f : HeightOneSpectrum R →₀ ℤ} :
-- imply
  fwdFun R K (bwdFun R K f) = f := by
-- proof
  apply SmoothCurveDivisors.fwd_bwd R K f

/--
[fwd_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothCurveDivisors.lean)
-/
@[path]
private lemma fwd_mul_eq
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {I J : (FractionalIdeal (nonZeroDivisors R) K)ˣ} :
-- imply
  fwdFun R K (I * J) = fwdFun R K I + fwdFun R K J := by
-- proof
  apply SmoothCurveDivisors.fwd_mul R K I J


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.DedekindDomain.FactorizationEquiv
open scoped nonZeroDivisors
open IsDedekindDomain
open FractionalIdeal


/--
[mem_unitsSupportFinset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean)
-/
@[path]
private lemma mem_unitsSupportFinset_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {K}
  {u : (FractionalIdeal R⁰ K)ˣ}
  {v : HeightOneSpectrum R} :
-- imply
  v ∈ unitsSupportFinset K u ↔ count K v (u : FractionalIdeal R⁰ K) ≠ 0 := by
-- proof
  apply FractionalIdeal.mem_unitsSupportFinset K u v

/--
[unitsToFinsupp_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean)
-/
@[path]
private lemma unitsToFinsupp_apply_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {K}
  {u : (FractionalIdeal R⁰ K)ˣ}
  {v : HeightOneSpectrum R} :
-- imply
  unitsToFinsupp K u v = count K v (u : FractionalIdeal R⁰ K) := by
-- proof
  apply FractionalIdeal.unitsToFinsupp_apply K u v

/--
[finsuppProd_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean)
-/
@[path]
private lemma finsuppProd_ne_zero_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {K}
  {e : HeightOneSpectrum R →₀ ℤ} :
-- imply
  e.prod (fun v n => (v.asIdeal : FractionalIdeal R⁰ K) ^ n) ≠ 0 := by
-- proof
  apply FractionalIdeal.finsuppProd_ne_zero K e

/--
[finsuppToUnits_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean)
-/
@[path]
private lemma finsuppToUnits_val_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {K}
  {e : HeightOneSpectrum R →₀ ℤ} :
-- imply
  (↑(finsuppToUnits K e) : FractionalIdeal R⁰ K) =
    e.prod (fun v n => (v.asIdeal : FractionalIdeal R⁰ K) ^ n) := by
-- proof
  apply FractionalIdeal.finsuppToUnits_val K e

/--
[count_finsuppToUnits](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean)
-/
@[path]
private lemma count_finsuppToUnits_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {K}
  {v : HeightOneSpectrum R}
  {e : HeightOneSpectrum R →₀ ℤ} :
-- imply
  count K v (↑(finsuppToUnits K e) : FractionalIdeal R⁰ K) = e v := by
-- proof
  apply FractionalIdeal.count_finsuppToUnits K v e

/--
[toUnits_left_inv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean)
-/
@[path]
private lemma toUnits_left_inv_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {K}
  {u : (FractionalIdeal R⁰ K)ˣ} :
-- imply
  finsuppToUnits K (unitsToFinsupp K u) = u := by
-- proof
  apply FractionalIdeal.toUnits_left_inv K u

/--
[toUnits_right_inv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean)
-/
@[path]
private lemma toUnits_right_inv_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {K}
  {e : HeightOneSpectrum R →₀ ℤ} :
-- imply
  unitsToFinsupp K (finsuppToUnits K e) = e := by
-- proof
  apply FractionalIdeal.toUnits_right_inv K e

/--
[unitsToFinsupp_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean)
-/
@[path]
private lemma unitsToFinsupp_mul_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {K}
  {u v : (FractionalIdeal R⁰ K)ˣ} :
-- imply
  unitsToFinsupp K (u * v) = unitsToFinsupp K u + unitsToFinsupp K v := by
-- proof
  apply FractionalIdeal.unitsToFinsupp_mul K u v

/--
[unitsToFinsupp_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean)
-/
@[path]
private lemma unitsToFinsupp_one_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {K} :
-- imply
  unitsToFinsupp K (1 : (FractionalIdeal R⁰ K)ˣ) = 0 := by
-- proof
  apply FractionalIdeal.unitsToFinsupp_one K

/--
[factorizationMulEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean)
-/
@[path]
private lemma factorizationMulEquiv_apply_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {K}
  {u : (FractionalIdeal R⁰ K)ˣ}
  {v : HeightOneSpectrum R} :
-- imply
  Multiplicative.toAdd (factorizationMulEquiv K u) v =
    count K v (u : FractionalIdeal R⁰ K) := by
-- proof
  apply FractionalIdeal.factorizationMulEquiv_apply K u v

/--
[factorizationMulEquiv_symm_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean)
-/
@[path]
private lemma factorizationMulEquiv_symm_val_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {K}
  {e : Multiplicative (HeightOneSpectrum R →₀ ℤ)} :
-- imply
  ((↑((factorizationMulEquiv K).symm e) : FractionalIdeal R⁰ K)) =
    (Multiplicative.toAdd e).prod (fun v n => (v.asIdeal : FractionalIdeal R⁰ K) ^ n) := by
-- proof
  apply FractionalIdeal.factorizationMulEquiv_symm_val K e

/--
[factorizationMulEquiv_prime_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean)
-/
@[path]
private lemma factorizationMulEquiv_prime_self_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {K}
  {w : HeightOneSpectrum R} :
-- imply
  Multiplicative.toAdd
    (factorizationMulEquiv K
    (Units.mk0 _ (coeIdeal_ne_zero.mpr w.ne_bot))) =
    Finsupp.single w 1 := by
-- proof
  apply FractionalIdeal.factorizationMulEquiv_prime_self K w

/--
[symm_single_zpow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean)
-/
@[path]
private lemma symm_single_zpow_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {K}
  {w : HeightOneSpectrum R}
  {n : ℤ} :
-- imply
  (↑((factorizationMulEquiv K).symm (Multiplicative.ofAdd (Finsupp.single w n))) :
    FractionalIdeal R⁰ K) = (w.asIdeal : FractionalIdeal R⁰ K) ^ n := by
-- proof
  apply FractionalIdeal.symm_single_zpow K w n


-- created on 2026-10-20

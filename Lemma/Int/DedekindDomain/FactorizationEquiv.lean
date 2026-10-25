import Mathlib
import sympy.Basic
import Def.RingTheory.DedekindDomain.FactorizationEquiv.Part4
open scoped nonZeroDivisors
open IsDedekindDomain
open FractionalIdeal


namespace FractionalIdeal

/--
[finsuppToUnits_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean)
-/
@[path]
lemma finsuppToUnits_val
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {K}
  {e : HeightOneSpectrum R →₀ ℤ} :
-- imply
  (↑(finsuppToUnits K e) : FractionalIdeal R⁰ K) =
    e.prod (fun v n => (v.asIdeal : FractionalIdeal R⁰ K) ^ n) :=
-- proof
  rfl

end FractionalIdeal

namespace FractionalIdeal

/--
[count_finsuppToUnits](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean)
-/
@[path]
lemma count_finsuppToUnits
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {K}
  {v : HeightOneSpectrum R}
  {e : HeightOneSpectrum R →₀ ℤ} :
-- imply
  count K v (↑(finsuppToUnits K e) : FractionalIdeal R⁰ K) = e v :=
-- proof
  count_finsuppProd K v e

end FractionalIdeal

namespace FractionalIdeal

/--
[unitsToFinsupp_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean)
-/
@[path]
lemma unitsToFinsupp_one
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {K} :
-- imply
  unitsToFinsupp K (1 : (FractionalIdeal R⁰ K)ˣ) = 0 := by
-- proof
  ext w
  rw [unitsToFinsupp_apply, Units.val_one, count_one K w, Finsupp.zero_apply]

end FractionalIdeal

namespace FractionalIdeal

/--
[factorizationMulEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean)
-/
@[path]
lemma factorizationMulEquiv_apply
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {K}
  {u : (FractionalIdeal R⁰ K)ˣ}
  {v : HeightOneSpectrum R} :
-- imply
  Multiplicative.toAdd (factorizationMulEquiv K u) v =
    count K v (u : FractionalIdeal R⁰ K) :=
-- proof
  rfl

end FractionalIdeal

namespace FractionalIdeal

/--
[factorizationMulEquiv_symm_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean)
-/
@[path]
lemma factorizationMulEquiv_symm_val
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {K}
  {e : Multiplicative (HeightOneSpectrum R →₀ ℤ)} :
-- imply
  ((↑((factorizationMulEquiv K).symm e) : FractionalIdeal R⁰ K)) =
    (Multiplicative.toAdd e).prod (fun v n => (v.asIdeal : FractionalIdeal R⁰ K) ^ n) :=
-- proof
  rfl

end FractionalIdeal

namespace FractionalIdeal

/--
[factorizationMulEquiv_prime_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean)
-/
@[path]
lemma factorizationMulEquiv_prime_self
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {K}
  {w : HeightOneSpectrum R} :
-- imply
  Multiplicative.toAdd
    (factorizationMulEquiv K
    (Units.mk0 _ (coeIdeal_ne_zero.mpr w.ne_bot))) =
    Finsupp.single w 1 := by
-- proof
  ext v
  classical
  rw [factorizationMulEquiv_apply, Units.val_mk0, count_maximal]
  split_ifs with h
  · rw [h, Finsupp.single_eq_same]
  · exact (Finsupp.single_eq_of_ne' h).symm

end FractionalIdeal

namespace FractionalIdeal

/--
[symm_single_zpow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean)
-/
@[path]
lemma symm_single_zpow
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {K}
  {w : HeightOneSpectrum R}
  {n : ℤ} :
-- imply
  (↑((factorizationMulEquiv K).symm (Multiplicative.ofAdd (Finsupp.single w n))) :
    FractionalIdeal R⁰ K) = (w.asIdeal : FractionalIdeal R⁰ K) ^ n := by
-- proof
  change (Finsupp.single w n).prod (fun v m => (v.asIdeal : FractionalIdeal R⁰ K) ^ m) = _
  exact Finsupp.prod_single_index (zpow_zero _)

end FractionalIdeal

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


-- created on 2026-10-20
-- updated on 2026-10-23

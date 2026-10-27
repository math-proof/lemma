import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.NumberTheoryI.code.IdealFactorization.Part3
open IsDedekindDomain


/--
[finsuppProd_primeIdealPow_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealFactorization.lean)
-/
@[path]
private lemma finsuppProd_primeIdealPow_ne_zero_eq
  [CommRing R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {exps : HeightOneSpectrum R →₀ ℤ} :
-- imply
  exps.prod (fun v e => (v.asIdeal : FractionalIdeal R⁰ K) ^ e) ≠ 0 := by
-- proof
  apply finsuppProd_primeIdealPow_ne_zero K exps

/--
[finsuppProd_countFinsupp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealFactorization.lean)
-/
@[path]
private lemma finsuppProd_countFinsupp_eq_eq
  [CommRing R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {I : (FractionalIdeal R⁰ K)ˣ} :
-- imply
  (countFinsupp K I).prod (fun v e => (v.asIdeal : FractionalIdeal R⁰ K) ^ e) = (I : FractionalIdeal R⁰ K) := by
-- proof
  apply finsuppProd_countFinsupp_eq K I

/--
[fractionalIdeal_mulEquiv_finsupp_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealFactorization.lean)
-/
@[path]
private lemma fractionalIdeal_mulEquiv_finsupp_apply_eq
  [CommRing R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {I : (FractionalIdeal R⁰ K)ˣ}
  {v : HeightOneSpectrum R} :
-- imply
  (Multiplicative.toAdd (fractionalIdeal_mulEquiv_finsupp K I)) v = FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) := by
-- proof
  apply fractionalIdeal_mulEquiv_finsupp_apply K I v

/--
[fractionalIdeal_mulEquiv_finsupp_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealFactorization.lean)
-/
@[path]
private lemma fractionalIdeal_mulEquiv_finsupp_symm_apply_eq
  [CommRing R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {exps : HeightOneSpectrum R →₀ ℤ} :
-- imply
  ((fractionalIdeal_mulEquiv_finsupp K).symm (Multiplicative.ofAdd exps) : FractionalIdeal R⁰ K) = exps.prod (fun v e => (v.asIdeal : FractionalIdeal R⁰ K) ^ e) := by
-- proof
  apply fractionalIdeal_mulEquiv_finsupp_symm_apply K exps


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Theorem.NumberTheory.NumberField.RayClass.FiniteCongruence.Part4
open scoped nonZeroDivisors
open NumberField
open Modulus


/--
[count_spanSingleton_add_ge_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/FiniteCongruence.lean)
-/
@[path]
private lemma count_spanSingleton_add_ge_of_ne_zero_eq
  [Field K] [NumberField K]
  {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
  {x y : K}
  {n : ℤ}
-- given
  (hxy : x + y ≠ 0)
  (hx : n ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x))
  (hy : n ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ y)) :
-- imply
  n ≤ FractionalIdeal.count K v
    (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x + y)) := by
-- proof
  apply NumberField.Modulus.count_spanSingleton_add_ge_of_ne_zero v hxy hx hy

/--
[rayElement_count_spanSingleton_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/FiniteCongruence.lean)
-/
@[path]
private lemma rayElement_count_spanSingleton_eq_zero_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : Kˣ}
  {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
-- given
  (hx : x ∈ rayElements m)
  (hv : finiteSupported m v) :
-- imply
  FractionalIdeal.count K v
    (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0 := by
-- proof
  apply NumberField.Modulus.rayElement_count_spanSingleton_eq_zero m x hx v hv

/--
[rayElement_valuation_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/FiniteCongruence.lean)
-/
@[path]
private lemma rayElement_valuation_eq_one_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m}
  {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
-- given
  (hv : finiteSupported m v) :
-- imply
  v.valuation K (((x : Kˣ) : K)) = 1 := by
-- proof
  apply NumberField.Modulus.rayElement_valuation_eq_one m x v hv

/--
[mem_rayElements_of_valuation_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/FiniteCongruence.lean)
-/
@[path]
private lemma mem_rayElements_of_valuation_eq_one_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {a : Kˣ}
-- given
  (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), finiteSupported m v → v.valuation K ((a : K)) = 1) :
-- imply
  a ∈ rayElements m := by
-- proof
  apply NumberField.Modulus.mem_rayElements_of_valuation_eq_one m a h

/--
[CongruentOneAtFinitePart.mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/FiniteCongruence.lean)
-/
@[path]
private lemma CongruentOneAtFinitePart_mul_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x y : Kˣ}
-- given
  (hx : CongruentOneAtFinitePart m x)
  (hy : CongruentOneAtFinitePart m y)
  (hmem : x ∈ rayElements m) :
-- imply
  CongruentOneAtFinitePart m (x * y) := by
-- proof
  apply NumberField.Modulus.CongruentOneAtFinitePart.mul hx hy hmem

/--
[CongruentOneAtFinitePart.inv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/FiniteCongruence.lean)
-/
@[path]
private lemma CongruentOneAtFinitePart_inv_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : Kˣ}
-- given
  (hx : CongruentOneAtFinitePart m x)
  (hmem : x ∈ rayElements m) :
-- imply
  CongruentOneAtFinitePart m x⁻¹ := by
-- proof
  apply NumberField.Modulus.CongruentOneAtFinitePart.inv hx hmem

/--
[mem_finiteRayOneElements_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/FiniteCongruence.lean)
-/
@[path]
private lemma mem_finiteRayOneElements_iff_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m} :
-- imply
  x ∈ finiteRayOneElements m ↔ CongruentOneAtFinitePart m (x : Kˣ) := by
-- proof
  apply NumberField.Modulus.mem_finiteRayOneElements_iff m x

/--
[exists_isUnit_mod_finitePart_div_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/FiniteCongruence.lean)
-/
@[path]
private lemma exists_isUnit_mod_finitePart_div_eq_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m} :
-- imply
  ∃ a b : 𝓞 K,
    IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) a) ∧
    IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b) ∧
    algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b = ((x : Kˣ) : K) := by
-- proof
  apply NumberField.Modulus.exists_isUnit_mod_finitePart_div_eq m x

/--
[quotientUnits_div_eq_of_div_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/FiniteCongruence.lean)
-/
@[path]
private lemma quotientUnits_div_eq_of_div_eq_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {a b c d : 𝓞 K}
-- given
  (ha : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) a))
  (hb : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b))
  (hc : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) c))
  (hd : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) d))
  (h : algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b = algebraMap (𝓞 K) K c / algebraMap (𝓞 K) K d) :
-- imply
  ha.unit * hb.unit⁻¹ = hc.unit * hd.unit⁻¹ := by
-- proof
  apply NumberField.Modulus.quotientUnits_div_eq_of_div_eq m a b c d ha hb hc hd h

/--
[finiteResidueMap_apply_of_div_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/FiniteCongruence.lean)
-/
@[path]
private lemma finiteResidueMap_apply_of_div_eq_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m}
  {a b : 𝓞 K}
-- given
  (ha : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) a))
  (hb : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b))
  (hab : algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b = ((x : Kˣ) : K)) :
-- imply
  finiteResidueMap m x = ha.unit * hb.unit⁻¹ := by
-- proof
  apply NumberField.Modulus.finiteResidueMap_apply_of_div_eq m x a b ha hb hab

/--
[finiteResidueMap_eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/FiniteCongruence.lean)
-/
@[path]
private lemma finiteResidueMap_eq_one_iff_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {x : rayElements m} :
-- imply
  finiteResidueMap m x = 1 ↔ CongruentOneAtFinitePart m (x : Kˣ) := by
-- proof
  apply NumberField.Modulus.finiteResidueMap_eq_one_iff m x

/--
[finiteResidueMap_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/FiniteCongruence.lean)
-/
@[path]
private lemma finiteResidueMap_ker_eq
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  (finiteResidueMap m).ker = finiteRayOneElements m := by
-- proof
  apply NumberField.Modulus.finiteResidueMap_ker m

/--
[finiteResidueMap_eq_one_of_valuation_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/FiniteCongruence.lean)
-/
@[path]
private lemma finiteResidueMap_eq_one_of_valuation_le_eq
  [Field K] [NumberField K]
  {m : Modulus K}
  {z : rayElements m}
-- given
  (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), finiteSupported m v → v.valuation K (((z : Kˣ) : K) - 1) ≤ WithZero.exp (-(finiteExponent m v))) :
-- imply
  finiteResidueMap m z = 1 := by
-- proof
  apply NumberField.Modulus.finiteResidueMap_eq_one_of_valuation_le m z h


-- created on 2026-10-20

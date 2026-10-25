/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/RayClass/FiniteCongruence.lean -/

import Theorem.NumberTheory.NumberField.RayClass.FiniteCongruence.Part4
import Lemma.Nat.NumberField.RayClass.FiniteCongruence
open scoped nonZeroDivisors


namespace NumberField

namespace Modulus

namespace FiniteCongruenceTest

variable {K : Type*} [Field K] [NumberField K]

/-- Direct generic application of the sum-count helper. -/
example (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {x y : K} {n : ℤ}
    (hxy : x + y ≠ 0)
    (hx : n ≤ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ x))
    (hy : n ≤ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ y)) :
    n ≤ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x + y)) :=
  count_spanSingleton_add_ge_of_ne_zero v hxy hx hy

/-- Zero-summand boundary: `0 + y = y` with nonzero sum uses the helper. -/
example (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {y : K} {n : ℤ}
    (hy0 : y ≠ 0)
    (h0 : n ≤ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (0 : K)))
    (hy : n ≤ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ y)) :
    n ≤ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ y) := by
  have hxy : (0 : K) + y ≠ 0 := by simpa using hy0
  have := count_spanSingleton_add_ge_of_ne_zero v hxy h0 hy
  simpa using this

/-- Direct API: finite-part congruence is closed under multiplication. -/
example (m : Modulus K) {x y : Kˣ}
    (hx : CongruentOneAtFinitePart m x)
    (hy : CongruentOneAtFinitePart m y)
    (hmem : x ∈ rayElements m) :
    CongruentOneAtFinitePart m (x * y) :=
  CongruentOneAtFinitePart.mul hx hy hmem

/-- Direct API: a ray element has count zero at supported places. -/
example (m : Modulus K) (x : Kˣ)
    (hx : x ∈ rayElements m)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hv : finiteSupported m v) :
    FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0 :=
  rayElement_count_spanSingleton_eq_zero m x hx v hv

/-- Direct API: finite-part congruence is closed under inversion. -/
example (m : Modulus K) {x : Kˣ}
    (hx : CongruentOneAtFinitePart m x)
    (hmem : x ∈ rayElements m) :
    CongruentOneAtFinitePart m x⁻¹ :=
  CongruentOneAtFinitePart.inv hx hmem

/-- Subgroup membership is exactly the finite-part congruence. -/
example (m : Modulus K) (x : rayElements m) :
    x ∈ finiteRayOneElements m ↔ CongruentOneAtFinitePart m (x : Kˣ) :=
  mem_finiteRayOneElements_iff m x

/-- The identity lies in the finite ray-one subgroup. -/
example (m : Modulus K) : (1 : rayElements m) ∈ finiteRayOneElements m := by
  rw [mem_finiteRayOneElements_iff]
  simpa using congruentOneAtFinitePart_one m

/-- Subgroup API: membership is closed under multiplication. -/
example (m : Modulus K) {a b : rayElements m}
    (ha : a ∈ finiteRayOneElements m)
    (hb : b ∈ finiteRayOneElements m) :
    a * b ∈ finiteRayOneElements m :=
  (finiteRayOneElements m).mul_mem ha hb

/-- Subgroup API: membership is closed under inversion. -/
example (m : Modulus K) {a : rayElements m}
    (ha : a ∈ finiteRayOneElements m) :
    a⁻¹ ∈ finiteRayOneElements m :=
  (finiteRayOneElements m).inv_mem ha

/-- Direct API: every ray element is a ratio of integers coprime to the finite part. -/
example (m : Modulus K) (x : rayElements m) :
    ∃ a b : 𝓞 K,
      IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) a) ∧
      IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b) ∧
      algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b = ((x : Kˣ) : K) :=
  exists_isUnit_mod_finitePart_div_eq m x

/-- Direct API: a ray element has valuation one at supported places. -/
example (m : Modulus K) (x : rayElements m)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hv : finiteSupported m v) :
    v.valuation K (((x : Kˣ) : K)) = 1 :=
  rayElement_valuation_eq_one m x v hv

/-- Consumer API: the coprimality witnesses give actual quotient units. -/
example (m : Modulus K) (x : rayElements m) :
    ∃ a b : 𝓞 K, ∃ ua ub : (𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K)))ˣ,
      (↑ua : 𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K))) =
        Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) a ∧
      (↑ub : 𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K))) =
        Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b ∧
      algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b = ((x : Kˣ) : K) := by
  obtain ⟨a, b, ha, hb, hdiv⟩ := exists_isUnit_mod_finitePart_div_eq m x
  exact ⟨a, b, ha.unit, hb.unit, ha.unit_spec, hb.unit_spec, hdiv⟩

/-- Direct API: residue map from any admissible numerator/denominator. -/
example (m : Modulus K) (x : rayElements m) (a b : 𝓞 K)
    (ha : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) a))
    (hb : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b))
    (hab : algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b =
      ((x : Kˣ) : K)) :
    finiteResidueMap m x = ha.unit * hb.unit⁻¹ :=
  finiteResidueMap_apply_of_div_eq m x a b ha hb hab

/-- MonoidHom API: the residue map preserves one. -/
example (m : Modulus K) :
    finiteResidueMap m (1 : rayElements m) = 1 :=
  map_one (finiteResidueMap m)

/-- MonoidHom API: the residue map preserves multiplication. -/
example (m : Modulus K) (x y : rayElements m) :
    finiteResidueMap m (x * y) =
      finiteResidueMap m x * finiteResidueMap m y :=
  map_mul (finiteResidueMap m) x y

/-- Kernel API: the residue map is trivial exactly on the congruence. -/
example (m : Modulus K) (x : rayElements m) :
    finiteResidueMap m x = 1 ↔ CongruentOneAtFinitePart m (x : Kˣ) :=
  finiteResidueMap_eq_one_iff m x

/-- Kernel API: the kernel of the residue map is the finite ray-one subgroup. -/
example (m : Modulus K) :
    (finiteResidueMap m).ker = finiteRayOneElements m :=
  finiteResidueMap_ker m

/-- Edge case: the residue map at the unit modulus is trivial. -/
example (x : rayElements (1 : Modulus K)) :
    finiteResidueMap 1 x = 1 := by
  rw [finiteResidueMap_eq_one_iff]
  intro v hv
  have htop : v.asIdeal = ⊤ := top_unique (by
    simpa [finiteSupported, one_finitePart] using hv)
  exact absurd htop v.isPrime.ne_top

/-- Direct API: valuation one at supported places gives a ray element. -/
example (m : Modulus K) (a : Kˣ)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      finiteSupported m v → v.valuation K ((a : K)) = 1) :
    a ∈ rayElements m :=
  mem_rayElements_of_valuation_eq_one m a h

/-- Round trip: the valuation criterion inverts `rayElement_valuation_eq_one`. -/
example (m : Modulus K) (x : rayElements m) : (x : Kˣ) ∈ rayElements m := by
  apply mem_rayElements_of_valuation_eq_one
  intro v hv
  exact rayElement_valuation_eq_one m x v hv

/-- Concrete: `1` is a ray element via the valuation criterion. -/
example (m : Modulus K) : (1 : Kˣ) ∈ rayElements m := by
  apply mem_rayElements_of_valuation_eq_one
  intro v _
  simp

/-- Boundary: at the unit modulus every unit is a ray element, since no finite
prime is supported and the valuation hypothesis holds vacuously. -/
example (a : Kˣ) : a ∈ rayElements (1 : Modulus K) := by
  apply mem_rayElements_of_valuation_eq_one
  intro v hv
  have htop : v.asIdeal = ⊤ := top_unique (by
    simpa [finiteSupported, one_finitePart] using hv)
  exact absurd htop v.isPrime.ne_top

/-- Direct API: a valuation bound on `z - 1` kills the residue map. -/
example (m : Modulus K) (z : rayElements m)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      finiteSupported m v →
        v.valuation K (((z : Kˣ) : K) - 1) ≤
          WithZero.exp (-(finiteExponent m v))) :
    finiteResidueMap m z = 1 :=
  finiteResidueMap_eq_one_of_valuation_le m z h

/-- Sanity case: `1` satisfies the conclusion through the new criterion. -/
example (m : Modulus K) : finiteResidueMap m (1 : rayElements m) = 1 := by
  apply finiteResidueMap_eq_one_of_valuation_le
  intro v hv
  have h0 : ((((1 : rayElements m) : Kˣ) : K) - 1) = 0 := by simp
  rw [h0, map_zero]
  exact bot_le

/-- Edge case: at the unit modulus the valuation hypothesis holds vacuously,
so the criterion gives triviality of the residue map. -/
example (z : rayElements (1 : Modulus K)) :
    finiteResidueMap 1 z = 1 := by
  apply finiteResidueMap_eq_one_of_valuation_le
  intro v hv
  have htop : v.asIdeal = ⊤ := top_unique (by
    simpa [finiteSupported, one_finitePart] using hv)
  exact absurd htop v.isPrime.ne_top

end FiniteCongruenceTest
end Modulus
end NumberField

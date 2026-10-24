import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.NumberTheory.Cyclotomic.CubicResidueSymbol
open MetaMathlibExtTest
open MetaMathlibExt Ideal NumberField


namespace MetaMathlibExtTest

/--
[test_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_zero
  [Field K]
  [NumberField K]
  {zeta : K}
  {a : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  cubicResidueSymbolRaw hZeta a 0 = 0 := by
-- proof
  unfold MetaMathlibExt.cubicResidueSymbolRaw
  simp
-- Unit law via associate invariance.

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_unit_mul_invariance](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_unit_mul_invariance
  [Field K]
  [NumberField K]
  {zeta : K}
  {a n : NumberField.RingOfIntegers K}
  {u : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hu : IsUnit u)
  (hn : n ≠ 0) :
-- imply
  cubicResidueSymbolRaw hZeta a (u * n) = cubicResidueSymbolRaw hZeta a n := by
-- proof
  have hu0 : u ≠ 0 := IsUnit.ne_zero hu
  have h1 := MetaMathlibExt.cubicResidueSymbolRaw_mul hZeta a u n hu0 hn
  have h2 := MetaMathlibExt.cubicResidueSymbolRaw_unit hZeta a u hu
  rwa [h2, one_mul] at h1

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_associate_invariance](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_associate_invariance
  [Field K]
  [NumberField K]
  {zeta : K}
  {a n : NumberField.RingOfIntegers K}
  {u : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hu : IsUnit u)
  (hn : n ≠ 0) :
-- imply
  cubicResidueSymbolRaw hZeta a n = cubicResidueSymbolRaw hZeta a (u * n) := by
-- proof
  rw [test_unit_mul_invariance hZeta a n u hu hn]

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_unit_via_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_unit_via_mul
  [Field K]
  [NumberField K]
  {zeta : K}
  {a : NumberField.RingOfIntegers K}
  {u : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hu : IsUnit u) :
-- imply
  cubicResidueSymbolRaw hZeta a u = 1 := by
-- proof
  have hOneNe : (1 : NumberField.RingOfIntegers K) ≠ 0 := one_ne_zero
  have hInv :=
    test_unit_mul_invariance hZeta a (1 : NumberField.RingOfIntegers K) u hu hOneNe
  have hOne :
    cubicResidueSymbolRaw hZeta a (1 : NumberField.RingOfIntegers K) = 1 :=
    MetaMathlibExt.cubicResidueSymbolRaw_unit hZeta a 1 isUnit_one
  rw [mul_one] at hInv
  rwa [hOne] at hInv
-- Prime root membership and congruence (not dividing case) — forwarded.

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_prime_not_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_prime_not_dvd
  [Field K]
  [NumberField K]
  {zeta : K}
  {a p : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hp : Prime p)
  (hp0 : p ≠ 0)
  (hCop : Nat.Coprime (Ideal.absNorm (Ideal.span ({p} : Set (NumberField.RingOfIntegers K)))) 3)
  (hndvd : ¬ p ∣ a) :
-- imply
  MetaMathlibExt.cubicResidueSymbolRaw hZeta a p ∈ ({(1 : NumberField.RingOfIntegers K), MetaMathlibExt.omega hZeta, MetaMathlibExt.omega hZeta ^ 2} : Set _) ∧ Ideal.Quotient.mk (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))) (MetaMathlibExt.cubicResidueSymbolRaw hZeta a p) = Ideal.Quotient.mk (Ideal.span ({p} : Set _)) a ^ ((Ideal.absNorm (Ideal.span ({p} : Set _)) - 1) / 3) :=
-- proof
  MetaMathlibExt.cubicResidueSymbolRaw_prime_not_dvd hZeta a p hp hp0 hCop hndvd
-- Prime zero when dividing — forwarded.

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_prime_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_prime_dvd
  [Field K]
  [NumberField K]
  {zeta : K}
  {a p : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hp : Prime p)
  (hp0 : p ≠ 0)
  (hCop : Nat.Coprime (Ideal.absNorm (Ideal.span ({p} : Set (NumberField.RingOfIntegers K)))) 3)
  (hdvd : p ∣ a) :
-- imply
  MetaMathlibExt.cubicResidueSymbolRaw hZeta a p = 0 :=
-- proof
  MetaMathlibExt.cubicResidueSymbolRaw_prime_dvd hZeta a p hp hp0 hCop hdvd
-- Multiplicativity: repeated factor and nontrivial composite — forwarded.

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_mul_repeated](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_mul_repeated
  [Field K]
  [NumberField K]
  {zeta : K}
  {a n : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hn : n ≠ 0) :
-- imply
  MetaMathlibExt.cubicResidueSymbolRaw hZeta a (n * n) = MetaMathlibExt.cubicResidueSymbolRaw hZeta a n * MetaMathlibExt.cubicResidueSymbolRaw hZeta a n :=
-- proof
  MetaMathlibExt.cubicResidueSymbolRaw_mul hZeta a n n hn hn

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_mul_composite_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_mul_composite_three
  [Field K]
  [NumberField K]
  {zeta : K}
  {a m n k : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hm : m ≠ 0)
  (hn : n ≠ 0)
  (hk : k ≠ 0) :
-- imply
  MetaMathlibExt.cubicResidueSymbolRaw hZeta a (m * n * k) = MetaMathlibExt.cubicResidueSymbolRaw hZeta a m * MetaMathlibExt.cubicResidueSymbolRaw hZeta a n * MetaMathlibExt.cubicResidueSymbolRaw hZeta a k := by
-- proof
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  have h1 := MetaMathlibExt.cubicResidueSymbolRaw_mul hZeta a (m * n) k hmn hk
  have h2 := MetaMathlibExt.cubicResidueSymbolRaw_mul hZeta a m n hm hn
  rwa [h2] at h1

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_mul_with_unit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_mul_with_unit
  [Field K]
  [NumberField K]
  {zeta : K}
  {a m n : NumberField.RingOfIntegers K}
  {u : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hu : IsUnit u)
  (hm : m ≠ 0)
  (hn : n ≠ 0) :
-- imply
  MetaMathlibExt.cubicResidueSymbolRaw hZeta a (u * m * n) = MetaMathlibExt.cubicResidueSymbolRaw hZeta a m * MetaMathlibExt.cubicResidueSymbolRaw hZeta a n := by
-- proof
  have hu0 : u ≠ 0 := IsUnit.ne_zero hu
  have hm0 : m ≠ 0 := hm
  have humn : u * m ≠ 0 := mul_ne_zero hu0 hm0
  have h1 := MetaMathlibExt.cubicResidueSymbolRaw_mul hZeta a (u * m) n humn hn
  have h2 := MetaMathlibExt.cubicResidueSymbolRaw_mul hZeta a u m hu0 hm0
  have h3 := MetaMathlibExt.cubicResidueSymbolRaw_unit hZeta a u hu
  rwa [h2, h3, one_mul] at h1
-- Totalization: every default branch of the prime-ideal factor — forwarded.

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_factor_notPrime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_factor_notPrime
  [Field K]
  [NumberField K]
  {zeta : K}
  {P : Ideal (NumberField.RingOfIntegers K)}
  {a : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hNotPrime : ¬ P.IsPrime) :
-- imply
  MetaMathlibExt.primeIdealCubicSymbolFactorRaw hZeta P a = 1 :=
-- proof
  MetaMathlibExt.primeIdealCubicSymbolFactorRaw_of_not_isPrime hZeta P a hNotPrime

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_factor_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_factor_bot
  [Field K]
  [NumberField K]
  {zeta : K}
  {a : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  MetaMathlibExt.primeIdealCubicSymbolFactorRaw hZeta (⊥ : Ideal (NumberField.RingOfIntegers K)) a = 1 :=
-- proof
  MetaMathlibExt.primeIdealCubicSymbolFactorRaw_bot hZeta a

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_factor_notCoprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_factor_notCoprime
  [Field K]
  [NumberField K]
  {zeta : K}
  {P : Ideal (NumberField.RingOfIntegers K)}
  {a : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hPprime : P.IsPrime)
  (hPbot : P ≠ ⊥)
  (hNotCop : ¬ Nat.Coprime (Ideal.absNorm P) 3) :
-- imply
  MetaMathlibExt.primeIdealCubicSymbolFactorRaw hZeta P a = 1 :=
-- proof
  MetaMathlibExt.primeIdealCubicSymbolFactorRaw_of_not_coprime
    hZeta P a hPprime hPbot hNotCop

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_factor_isPrime_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_factor_isPrime_bot
  [Field K]
  [NumberField K]
  {zeta : K}
  {P : Ideal (NumberField.RingOfIntegers K)}
  {a : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hPprime : P.IsPrime)
  (hBot : P = ⊥) :
-- imply
  MetaMathlibExt.primeIdealCubicSymbolFactorRaw hZeta P a = 1 :=
-- proof
  MetaMathlibExt.primeIdealCubicSymbolFactorRaw_eq_one_of_isPrime_of_bot
    hZeta P a hPprime hBot
-- Independent definition-unfolding probes for prime-ideal factor branches.

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_factor_valid_branch_via_definition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_factor_valid_branch_via_definition
  [Field K]
  [NumberField K]
  {zeta : K}
  {P : Ideal (NumberField.RingOfIntegers K)}
  {a : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hPprime : P.IsPrime)
  (hPbot : P ≠ ⊥)
  (hCop : Nat.Coprime (Ideal.absNorm P) 3)
  (ha : a ∉ P) :
-- imply
  MetaMathlibExt.primeIdealCubicSymbolFactorRaw hZeta P a = MetaMathlibExt.primeIdealValidCubicSymbol hZeta P a hPprime hPbot hCop ha := by
-- proof
  simp only [MetaMathlibExt.primeIdealCubicSymbolFactorRaw,
    dite_eq_left hPprime, dite_eq_left hPbot, dite_eq_left hCop, dite_eq_right ha]

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_factor_dvd_branch_via_definition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_factor_dvd_branch_via_definition
  [Field K]
  [NumberField K]
  {zeta : K}
  {P : Ideal (NumberField.RingOfIntegers K)}
  {a : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hPprime : P.IsPrime)
  (hPbot : P ≠ ⊥)
  (hCop : Nat.Coprime (Ideal.absNorm P) 3)
  (ha : a ∈ P) :
-- imply
  MetaMathlibExt.primeIdealCubicSymbolFactorRaw hZeta P a = 0 := by
-- proof
  simp only [MetaMathlibExt.primeIdealCubicSymbolFactorRaw,
    dite_eq_left hPprime, dite_eq_left hPbot, dite_eq_left hCop, dite_eq_left ha]

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_factor_notPrime_via_definition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_factor_notPrime_via_definition
  [Field K]
  [NumberField K]
  {zeta : K}
  {P : Ideal (NumberField.RingOfIntegers K)}
  {a : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hNotPrime : ¬ P.IsPrime) :
-- imply
  MetaMathlibExt.primeIdealCubicSymbolFactorRaw hZeta P a = 1 := by
-- proof
  simp only [MetaMathlibExt.primeIdealCubicSymbolFactorRaw, dite_eq_right hNotPrime]

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_factor_bot_via_definition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_factor_bot_via_definition
  [Field K]
  [NumberField K]
  {zeta : K}
  {a : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  MetaMathlibExt.primeIdealCubicSymbolFactorRaw hZeta (⊥ : Ideal (NumberField.RingOfIntegers K)) a = 1 := by
-- proof
  have hPprime : (⊥ : Ideal (NumberField.RingOfIntegers K)).IsPrime := by
    constructor
    · intro h
      have : (1 : NumberField.RingOfIntegers K) ∈ (⊥ : Ideal _) := by
        rw [h]; trivial
      simp at this
    · intro x y hxy
      rw [Ideal.mem_bot] at hxy
      rcases mul_eq_zero.mp hxy with hx | hy
      · left; rw [Ideal.mem_bot, hx]
      · right; rw [Ideal.mem_bot, hy]
  have hNotBot : ¬ ((⊥ : Ideal (NumberField.RingOfIntegers K)) ≠ ⊥) := by
    intro h
    exact h rfl
  simp only [MetaMathlibExt.primeIdealCubicSymbolFactorRaw, dite_eq_left hPprime, dite_eq_right hNotBot]

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_factor_notCoprime_via_definition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_factor_notCoprime_via_definition
  [Field K]
  [NumberField K]
  {zeta : K}
  {P : Ideal (NumberField.RingOfIntegers K)}
  {a : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hPprime : P.IsPrime)
  (hPbot : P ≠ ⊥)
  (hNotCop : ¬ Nat.Coprime (Ideal.absNorm P) 3) :
-- imply
  MetaMathlibExt.primeIdealCubicSymbolFactorRaw hZeta P a = 1 := by
-- proof
  simp only [MetaMathlibExt.primeIdealCubicSymbolFactorRaw,
    dite_eq_left hPprime, dite_eq_left hPbot, dite_eq_right hNotCop]
-- Independent definition-unfolding probe for prime denominator via normalizedFactors.

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_prime_not_dvd_via_definition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_prime_not_dvd_via_definition
  [Field K]
  [NumberField K]
  {zeta : K}
  {a p : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hp : Prime p)
  (hp0 : p ≠ 0)
  (hCop : Nat.Coprime (Ideal.absNorm (Ideal.span ({p} : Set (NumberField.RingOfIntegers K)))) 3)
  (hndvd : ¬ p ∣ a) :
-- imply
  MetaMathlibExt.cubicResidueSymbolRaw hZeta a p ∈ ({(1 : NumberField.RingOfIntegers K), MetaMathlibExt.omega hZeta, MetaMathlibExt.omega hZeta ^ 2} : Set _) ∧ Ideal.Quotient.mk (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))) (MetaMathlibExt.cubicResidueSymbolRaw hZeta a p) = Ideal.Quotient.mk (Ideal.span ({p} : Set _)) a ^ ((Ideal.absNorm (Ideal.span ({p} : Set _)) - 1) / 3) := by
-- proof
  have hNotMem : a ∉ Ideal.span ({p} : Set (NumberField.RingOfIntegers K)) := by
    rwa [Ideal.mem_span_singleton]
  have hSpanPrime : (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hp
  have hSpanNeBot : Ideal.span ({p} : Set (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hPrimeIdeal : Prime (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))) :=
    Ideal.prime_of_isPrime hSpanNeBot hSpanPrime
  have hIrred : Irreducible (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))) :=
    hPrimeIdeal.irreducible
  have hFac : UniqueFactorizationMonoid.normalizedFactors
    (Ideal.span ({p} : Set _)) = {Ideal.span {p}} := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hIrred, normalize_eq]
  have hSymEq : MetaMathlibExt.cubicResidueSymbolRaw hZeta a p =
    MetaMathlibExt.primeIdealValidCubicSymbol hZeta
      (Ideal.span ({p} : Set _)) a hSpanPrime hSpanNeBot hCop hNotMem := by
    unfold MetaMathlibExt.cubicResidueSymbolRaw
    simp only [hp0, ↓reduceIte]
    rw [hFac]
    simp only [Multiset.map_singleton, Multiset.prod_singleton]
    simp only [MetaMathlibExt.primeIdealCubicSymbolFactorRaw,
      dite_eq_left hSpanPrime, dite_eq_left hSpanNeBot, dite_eq_left hCop, dite_eq_right hNotMem]
  rw [hSymEq]
  exact ⟨MetaMathlibExt.primeIdealValidCubicSymbol_mem hZeta _ _
    hSpanPrime hSpanNeBot hCop hNotMem,
    MetaMathlibExt.primeIdealValidCubicSymbol_spec hZeta _ _
      hSpanPrime hSpanNeBot hCop hNotMem⟩

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_prime_dvd_via_definition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_prime_dvd_via_definition
  [Field K]
  [NumberField K]
  {zeta : K}
  {a p : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hp : Prime p)
  (hp0 : p ≠ 0)
  (hCop : Nat.Coprime (Ideal.absNorm (Ideal.span ({p} : Set (NumberField.RingOfIntegers K)))) 3)
  (hdvd : p ∣ a) :
-- imply
  MetaMathlibExt.cubicResidueSymbolRaw hZeta a p = 0 := by
-- proof
  have hMem : a ∈ Ideal.span ({p} : Set (NumberField.RingOfIntegers K)) :=
    Ideal.mem_span_singleton.mpr hdvd
  have hSpanPrime : (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hp
  have hSpanNeBot : Ideal.span ({p} : Set (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hPrimeIdeal : Prime (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))) :=
    Ideal.prime_of_isPrime hSpanNeBot hSpanPrime
  have hIrred : Irreducible (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))) :=
    hPrimeIdeal.irreducible
  have hFac : UniqueFactorizationMonoid.normalizedFactors
    (Ideal.span ({p} : Set _)) = {Ideal.span {p}} := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hIrred, normalize_eq]
  unfold MetaMathlibExt.cubicResidueSymbolRaw
  simp only [hp0, ↓reduceIte]
  rw [hFac]
  simp only [Multiset.map_singleton, Multiset.prod_singleton]
  simp only [MetaMathlibExt.primeIdealCubicSymbolFactorRaw,
    dite_eq_left hSpanPrime, dite_eq_left hSpanNeBot, dite_eq_left hCop, dite_eq_left hMem]
-- Independent direct-definition multiplicativity probes that unfold normalizedFactors.

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_mul_via_definition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_mul_via_definition
  [Field K]
  [NumberField K]
  {zeta : K}
  {a m n : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hm : m ≠ 0)
  (hn : n ≠ 0) :
-- imply
  MetaMathlibExt.cubicResidueSymbolRaw hZeta a (m * n) = MetaMathlibExt.cubicResidueSymbolRaw hZeta a m * MetaMathlibExt.cubicResidueSymbolRaw hZeta a n := by
-- proof
  unfold MetaMathlibExt.cubicResidueSymbolRaw
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  simp only [hm, hn, hmn, ↓reduceIte]
  have hSpanMul : Ideal.span ({m * n} : Set (NumberField.RingOfIntegers K)) =
    Ideal.span ({m} : Set _) * Ideal.span ({n} : Set _) := by
    rw [Ideal.span_singleton_mul_span_singleton]
  have hmBot : Ideal.span ({m} : Set (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hnBot : Ideal.span ({n} : Set (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hFacMul : UniqueFactorizationMonoid.normalizedFactors
    (Ideal.span ({m * n} : Set _)) =
    UniqueFactorizationMonoid.normalizedFactors (Ideal.span ({m} : Set _)) +
      UniqueFactorizationMonoid.normalizedFactors (Ideal.span ({n} : Set _)) := by
    rw [hSpanMul]
    exact UniqueFactorizationMonoid.normalizedFactors_mul hmBot hnBot
  simp only [hFacMul, Multiset.map_add, Multiset.prod_add]

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_mul_repeated_via_definition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_mul_repeated_via_definition
  [Field K]
  [NumberField K]
  {zeta : K}
  {a n : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hn : n ≠ 0) :
-- imply
  MetaMathlibExt.cubicResidueSymbolRaw hZeta a (n * n) = MetaMathlibExt.cubicResidueSymbolRaw hZeta a n * MetaMathlibExt.cubicResidueSymbolRaw hZeta a n := by
-- proof
  have h := test_mul_via_definition hZeta a n n hn hn
  simpa using h

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_mul_composite_three_via_definition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_mul_composite_three_via_definition
  [Field K]
  [NumberField K]
  {zeta : K}
  {a m n k : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hm : m ≠ 0)
  (hn : n ≠ 0)
  (hk : k ≠ 0) :
-- imply
  MetaMathlibExt.cubicResidueSymbolRaw hZeta a (m * n * k) = MetaMathlibExt.cubicResidueSymbolRaw hZeta a m * MetaMathlibExt.cubicResidueSymbolRaw hZeta a n * MetaMathlibExt.cubicResidueSymbolRaw hZeta a k := by
-- proof
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  have h1 := test_mul_via_definition hZeta a (m * n) k hmn hk
  have h2 := test_mul_via_definition hZeta a m n hm hn
  rwa [h2] at h1

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concrete_cyclotomic_inhabited](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concrete_cyclotomic_inhabited
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
-- proof
  inferInstance

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concrete_zeta_isPrimitive](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concrete_zeta_isPrimitive
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  IsPrimitiveRoot concreteZeta 3 :=
-- proof
  IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ)

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concrete_omega_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concrete_omega_mem
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  MetaMathlibExt.omega (K := CyclotomicField 3 ℚ) concrete_zeta_isPrimitive ∈ ({(1 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)), MetaMathlibExt.omega concrete_zeta_isPrimitive, MetaMathlibExt.omega concrete_zeta_isPrimitive ^ 2} : Set _) := by
-- proof
  simp

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concrete_symbol_at_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concrete_symbol_at_one
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  MetaMathlibExt.cubicResidueSymbolRaw (K := CyclotomicField 3 ℚ) concrete_zeta_isPrimitive 0 1 = 1 :=
-- proof
  MetaMathlibExt.cubicResidueSymbolRaw_unit
    concrete_zeta_isPrimitive 0 1 isUnit_one

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concrete_symbol_zero_branch](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concrete_symbol_zero_branch
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  MetaMathlibExt.cubicResidueSymbolRaw (K := CyclotomicField 3 ℚ) concrete_zeta_isPrimitive 0 0 = 0 := by
-- proof
  unfold MetaMathlibExt.cubicResidueSymbolRaw
  simp

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concrete_symbol_unit_direct](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concrete_symbol_unit_direct
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  MetaMathlibExt.cubicResidueSymbolRaw (K := CyclotomicField 3 ℚ) concrete_zeta_isPrimitive 0 (-1) = 1 := by
-- proof
  have h : IsUnit (-1 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) :=
    isUnit_one.neg
  exact MetaMathlibExt.cubicResidueSymbolRaw_unit concrete_zeta_isPrimitive 0 (-1) h
-- Concrete composite and repeated-factor probes via direct definition

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concrete_composite_mul_via_definition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concrete_composite_mul_via_definition
  [Field K]
  [NumberField K]
  {zeta : K}
  {a : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)}
  {m n : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hm : m ≠ 0)
  (hn : n ≠ 0) :
-- imply
  MetaMathlibExt.cubicResidueSymbolRaw (K := CyclotomicField 3 ℚ) concrete_zeta_isPrimitive a (m * n) = MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a m * MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a n :=
-- proof
  test_mul_via_definition concrete_zeta_isPrimitive a m n hm hn

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concrete_repeated_factor_via_definition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concrete_repeated_factor_via_definition
  [Field K]
  [NumberField K]
  {zeta : K}
  {a n : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hn : n ≠ 0) :
-- imply
  MetaMathlibExt.cubicResidueSymbolRaw (K := CyclotomicField 3 ℚ) concrete_zeta_isPrimitive a (n * n) = MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a n * MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a n :=
-- proof
  test_mul_repeated_via_definition concrete_zeta_isPrimitive a n hn
-- Concrete composite with explicit nonzero numerals (exercises normalization multiplicity)

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concrete_composite_explicit_two_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concrete_composite_explicit_two_three
  [Field K]
  [NumberField K]
  {zeta : K}
  {a : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  MetaMathlibExt.cubicResidueSymbolRaw (K := CyclotomicField 3 ℚ) concrete_zeta_isPrimitive a ((2 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) * 3) = MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a 2 * MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a 3 := by
-- proof
  have h2 : (2 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by decide : (2 : ℕ) ≠ 0)
  have h3 : (3 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by decide : (3 : ℕ) ≠ 0)
  exact test_mul_via_definition concrete_zeta_isPrimitive a 2 3 h2 h3

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concrete_repeated_explicit_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concrete_repeated_explicit_two
  [Field K]
  [NumberField K]
  {zeta : K}
  {a : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  MetaMathlibExt.cubicResidueSymbolRaw (K := CyclotomicField 3 ℚ) concrete_zeta_isPrimitive a ((2 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) * 2) = MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a 2 * MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a 2 := by
-- proof
  have h2 : (2 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by decide : (2 : ℕ) ≠ 0)
  exact test_mul_via_definition concrete_zeta_isPrimitive a 2 2 h2 h2
-- Closed concrete prime over rational prime 2

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concretePrimeIdeal_isPrime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concretePrimeIdeal_isPrime
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  concretePrimeIdeal.IsPrime :=
-- proof
  concretePrimeIdealSubtype.prop.1

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concretePrimeIdeal_liesOver](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concretePrimeIdeal_liesOver
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  concretePrimeIdeal.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) :=
-- proof
  concretePrimeIdealSubtype.prop.2

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concretePrimeIdeal_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concretePrimeIdeal_mem
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  concretePrimeIdeal ∈ Ideal.primesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) :=
-- proof
  concretePrimeIdealSubtype.prop

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concretePrimeIdeal_ne_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concretePrimeIdeal_ne_bot
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  concretePrimeIdeal ≠ ⊥ :=
-- proof
  Ideal.ne_bot_of_mem_primesOver
    (p := Ideal.span ({(2 : ℤ)} : Set ℤ))
    (by
      intro h
      have hMem : (2 : ℤ) ∈ (⊥ : Ideal ℤ) :=
        h ▸ Ideal.mem_span_singleton_self (2 : ℤ)
      simp at hMem)
    concretePrimeIdeal_mem

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concretePrimeIdeal_inertiaDeg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concretePrimeIdeal_inertiaDeg
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  Ideal.inertiaDeg concretePrimeIdeal ℤ = 2 := by
-- proof
  have hm : ¬ (2 : ℕ) ∣ 3 := by decide
  have hEq :
    Ideal.inertiaDeg concretePrimeIdeal ℤ =
      orderOf ((2 : ℕ) : ZMod 3) :=
    @IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
      (m := 3) (p := 2) _ (CyclotomicField 3 ℚ) _ _
      concretePrimeIdeal concretePrimeIdeal_isPrime
      concretePrimeIdeal_liesOver _ _ hm
  have hOrder : orderOf ((2 : ℕ) : ZMod 3) = 2 := by
    apply orderOf_eq_prime
    · decide
    · decide
  rwa [hOrder] at hEq

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concretePrimeIdeal_absNorm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concretePrimeIdeal_absNorm
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  Ideal.absNorm concretePrimeIdeal = 4 := by
-- proof
  have hInertia := concretePrimeIdeal_inertiaDeg
  have hPow :
    (2 : ℕ) ^ Ideal.inertiaDeg concretePrimeIdeal ℤ =
      Ideal.absNorm concretePrimeIdeal :=
    @Ideal.pow_inertiaDeg _ _ _ _ _ 2 concretePrimeIdeal
      concretePrimeIdeal_isPrime concretePrimeIdeal_liesOver
  rw [hInertia] at hPow
  have : (2 : ℕ) ^ 2 = 4 := by decide
  rwa [this] at hPow

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concretePrimeIdeal_norm_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concretePrimeIdeal_norm_coprime
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  Nat.Coprime (Ideal.absNorm concretePrimeIdeal) 3 := by
-- proof
  rw [concretePrimeIdeal_absNorm]
  decide

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concretePrime_span](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concretePrime_span
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  Ideal.span ({concretePrime} : Set _) = concretePrimeIdeal :=
-- proof
  Submodule.IsPrincipal.span_singleton_generator concretePrimeIdeal

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concretePrime_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concretePrime_prime
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  Prime concretePrime :=
-- proof
  @Submodule.IsPrincipal.prime_generator_of_isPrime _ _
    concretePrimeIdeal _ concretePrimeIdeal_isPrime
    concretePrimeIdeal_ne_bot

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concretePrime_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concretePrime_ne_zero
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  concretePrime ≠ 0 :=
-- proof
  concretePrime_prime.ne_zero

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concretePrime_absNorm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concretePrime_absNorm
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  Ideal.absNorm (Ideal.span ({concretePrime} : Set _)) = 4 := by
-- proof
  rw [concretePrime_span, concretePrimeIdeal_absNorm]

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concretePrime_norm_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concretePrime_norm_coprime
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  Nat.Coprime (Ideal.absNorm (Ideal.span ({concretePrime} : Set _))) 3 := by
-- proof
  rw [concretePrime_absNorm]
  decide

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concretePrime_not_dvd_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concretePrime_not_dvd_one
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  ¬ concretePrime ∣ (1 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) := by
-- proof
  intro h
  have hUnit : IsUnit concretePrime := isUnit_of_dvd_one h
  exact concretePrime_prime.not_isUnit hUnit

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concretePrime_not_mem_span_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concretePrime_not_mem_span_one
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  (1 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) ∉ Ideal.span ({concretePrime} : Set _) := by
-- proof
  rwa [Ideal.mem_span_singleton]

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concretePrime_one_not_mem_ideal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concretePrime_one_not_mem_ideal
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  (1 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) ∉ concretePrimeIdeal := by
-- proof
  rwa [← concretePrime_span]
-- Closed concrete valid-branch probe at prime denominator

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concrete_prime_symbol_valid_closed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concrete_prime_symbol_valid_closed
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  MetaMathlibExt.cubicResidueSymbolRaw (K := CyclotomicField 3 ℚ) concrete_zeta_isPrimitive 1 concretePrime ∈ ({(1 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)), MetaMathlibExt.omega concrete_zeta_isPrimitive, MetaMathlibExt.omega concrete_zeta_isPrimitive ^ 2} : Set _) ∧ Ideal.Quotient.mk (Ideal.span {concretePrime}) (MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive 1 concretePrime) = Ideal.Quotient.mk (Ideal.span {concretePrime}) (1 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) ^ ((Ideal.absNorm (Ideal.span {concretePrime}) - 1) / 3) :=
-- proof
  MetaMathlibExt.cubicResidueSymbolRaw_prime_not_dvd
    (K := CyclotomicField 3 ℚ) concrete_zeta_isPrimitive 1 concretePrime
    concretePrime_prime concretePrime_ne_zero concretePrime_norm_coprime
    concretePrime_not_dvd_one
-- Valid branch via direct definition unfolding (closed)

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concrete_prime_symbol_valid_via_definition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concrete_prime_symbol_valid_via_definition
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  MetaMathlibExt.cubicResidueSymbolRaw (K := CyclotomicField 3 ℚ) concrete_zeta_isPrimitive 1 concretePrime ∈ ({(1 : _), MetaMathlibExt.omega concrete_zeta_isPrimitive, MetaMathlibExt.omega concrete_zeta_isPrimitive ^ 2} : Set _) ∧ Ideal.Quotient.mk (Ideal.span {concretePrime}) (MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive 1 concretePrime) = Ideal.Quotient.mk (Ideal.span {concretePrime}) (1 : _) ^ ((Ideal.absNorm (Ideal.span {concretePrime}) - 1) / 3) := by
-- proof
  have hNotMem : (1 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) ∉
    Ideal.span ({concretePrime} : Set _) := concretePrime_not_mem_span_one
  have hSpanPrime :
    (Ideal.span ({concretePrime} : Set _)).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime concretePrime_prime
  have hSpanNeBot :
    Ideal.span ({concretePrime} : Set _) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hCop := concretePrime_norm_coprime
  have hFac :
    UniqueFactorizationMonoid.normalizedFactors
      (Ideal.span ({concretePrime} : Set _)) =
      {Ideal.span {concretePrime}} := by
    have hPrimeIdeal :
      Prime (Ideal.span ({concretePrime} : Set _)) :=
      Ideal.prime_of_isPrime hSpanNeBot hSpanPrime
    have hIrr :
      Irreducible (Ideal.span ({concretePrime} : Set _)) :=
      hPrimeIdeal.irreducible
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hIrr,
      normalize_eq]
  have hSymEq :
    MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive 1
      concretePrime =
      MetaMathlibExt.primeIdealValidCubicSymbol
        (K := CyclotomicField 3 ℚ) concrete_zeta_isPrimitive
        (Ideal.span {concretePrime}) 1 hSpanPrime hSpanNeBot
        hCop hNotMem := by
    unfold MetaMathlibExt.cubicResidueSymbolRaw
    simp only [concretePrime_ne_zero, ↓reduceIte]
    rw [hFac]
    simp only [Multiset.map_singleton, Multiset.prod_singleton]
    simp only [MetaMathlibExt.primeIdealCubicSymbolFactorRaw,
      dite_eq_left hSpanPrime, dite_eq_left hSpanNeBot, dite_eq_left hCop,
      dite_eq_right hNotMem]
  rw [hSymEq]
  exact ⟨MetaMathlibExt.primeIdealValidCubicSymbol_mem _ _ _
    hSpanPrime hSpanNeBot hCop hNotMem,
    MetaMathlibExt.primeIdealValidCubicSymbol_spec _ _ _
      hSpanPrime hSpanNeBot hCop hNotMem⟩
-- NormalizedFactors factorization for the concrete prime

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concretePrime_normalizedFactors_single](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concretePrime_normalizedFactors_single
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  UniqueFactorizationMonoid.normalizedFactors (Ideal.span ({concretePrime} : Set (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)))) = {Ideal.span {concretePrime}} := by
-- proof
  have hSpanNeBot :
    Ideal.span ({concretePrime} :
      Set (NumberField.RingOfIntegers (CyclotomicField 3 ℚ))) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hSpanPrime :
    (Ideal.span ({concretePrime} : Set _)).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime concretePrime_prime
  have hPrimeIdeal :
    Prime (Ideal.span ({concretePrime} : Set _)) :=
    Ideal.prime_of_isPrime hSpanNeBot hSpanPrime
  have hIrr :
    Irreducible (Ideal.span ({concretePrime} : Set _)) :=
    hPrimeIdeal.irreducible
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hIrr,
    normalize_eq]

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concretePrime_normalizedFactors_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concretePrime_normalizedFactors_sq
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  UniqueFactorizationMonoid.normalizedFactors (Ideal.span ({concretePrime * concretePrime} : Set (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)))) = {Ideal.span {concretePrime}, Ideal.span {concretePrime}} := by
-- proof
  have hPiNeZero := concretePrime_ne_zero
  have hBot :
    Ideal.span ({concretePrime} :
      Set (NumberField.RingOfIntegers (CyclotomicField 3 ℚ))) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hFacSingle := concretePrime_normalizedFactors_single
  have hFacMul :
    UniqueFactorizationMonoid.normalizedFactors
      (Ideal.span ({concretePrime * concretePrime} : Set _)) =
      UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({concretePrime} : Set _)) +
        UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({concretePrime} : Set _)) := by
    rw [show Ideal.span ({concretePrime * concretePrime} : Set _) =
      Ideal.span ({concretePrime} : Set _) *
        Ideal.span ({concretePrime} : Set _) from by
      rw [Ideal.span_singleton_mul_span_singleton]]
    exact UniqueFactorizationMonoid.normalizedFactors_mul hBot hBot
  rw [hFacMul, hFacSingle]
  rfl
-- Closed repeated-factor probe using the concrete prime twice,
-- unfolding normalizedFactors (nontrivial factorization)

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concrete_prime_repeated_closed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concrete_prime_repeated_closed
  [Field K]
  [NumberField K]
  {zeta : K}
  {a : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a (concretePrime * concretePrime) = MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a concretePrime * MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive a concretePrime := by
-- proof
  have hPiNeZero : concretePrime ≠ 0 := concretePrime_ne_zero
  have hPiSqNeZero : concretePrime * concretePrime ≠ 0 :=
    mul_ne_zero hPiNeZero hPiNeZero
  unfold MetaMathlibExt.cubicResidueSymbolRaw
  simp only [hPiNeZero, hPiSqNeZero, ↓reduceIte]
  have hSpanMul :
    Ideal.span ({concretePrime * concretePrime} :
      Set (NumberField.RingOfIntegers (CyclotomicField 3 ℚ))) =
      Ideal.span ({concretePrime} : Set _) *
        Ideal.span ({concretePrime} : Set _) := by
    rw [Ideal.span_singleton_mul_span_singleton]
  have hBot :
    Ideal.span ({concretePrime} :
      Set (NumberField.RingOfIntegers (CyclotomicField 3 ℚ))) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hFacMul :
    UniqueFactorizationMonoid.normalizedFactors
      (Ideal.span ({concretePrime * concretePrime} : Set _)) =
      UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({concretePrime} : Set _)) +
        UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({concretePrime} : Set _)) := by
    rw [hSpanMul]
    exact UniqueFactorizationMonoid.normalizedFactors_mul hBot hBot
  simp only [hFacMul, Multiset.map_add, Multiset.prod_add]

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[concrete_prime_repeated_zero_a_closed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma concrete_prime_repeated_zero_a_closed
  [Field K]
  [NumberField K]
  {zeta : K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive (0 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) (concretePrime * concretePrime) = MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive 0 concretePrime * MetaMathlibExt.cubicResidueSymbolRaw concrete_zeta_isPrimitive 0 concretePrime :=
-- proof
  concrete_prime_repeated_closed 0

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_valid_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_valid_ne_zero
  [Field K]
  [NumberField K]
  {zeta : K}
  {n : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  MetaMathlibExt.IsCubicResidueDenominator n → n ≠ 0 :=
-- proof
  fun h => h.1

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_valid_norm_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_valid_norm_coprime
  [Field K]
  [NumberField K]
  {zeta : K}
  {n : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  MetaMathlibExt.IsCubicResidueDenominator n → Nat.Coprime (Ideal.absNorm (Ideal.span {n})) 3 :=
-- proof
  fun h => h.2

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_canonical_eq_raw](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_canonical_eq_raw
  [Field K]
  [NumberField K]
  {zeta : K}
  {a n : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  ∀ (hValid : MetaMathlibExt.IsCubicResidueDenominator n), MetaMathlibExt.cubicResidueSymbol hZeta a n hValid = MetaMathlibExt.cubicResidueSymbolRaw hZeta a n :=
-- proof
  fun _ => rfl

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_canonical_prime_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_canonical_prime_dvd
  [Field K]
  [NumberField K]
  {zeta : K}
  {a p : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  ∀ (_hp : Prime p) (hpValid : MetaMathlibExt.IsCubicResidueDenominator p), p ∣ a → MetaMathlibExt.cubicResidueSymbol hZeta a p hpValid = 0 :=
-- proof
  fun _hp hpValid hdvd =>
    MetaMathlibExt.cubicResidueSymbol_prime_dvd hZeta a p _hp hpValid hdvd

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[test_canonical_prime_not_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma test_canonical_prime_not_dvd
  [Field K]
  [NumberField K]
  {zeta : K}
  {a p : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  ∀ (_hp : Prime p) (hpValid : MetaMathlibExt.IsCubicResidueDenominator p), ¬ p ∣ a → MetaMathlibExt.cubicResidueSymbol hZeta a p hpValid ∈ ({(1 : NumberField.RingOfIntegers K), MetaMathlibExt.omega hZeta, MetaMathlibExt.omega hZeta ^ 2} : Set _) ∧ Ideal.Quotient.mk (Ideal.span {p}) (MetaMathlibExt.cubicResidueSymbol hZeta a p hpValid) = Ideal.Quotient.mk (Ideal.span {p}) a ^ ((Ideal.absNorm (Ideal.span {p}) - 1) / 3) :=
-- proof
  fun _hp hpValid hndvd =>
    MetaMathlibExt.cubicResidueSymbol_prime_not_dvd hZeta a p _hp hpValid hndvd

end MetaMathlibExtTest


-- created on 2026-10-23

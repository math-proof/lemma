import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.Cyclotomic.CubicResidueSymbol
open MetaMathlibExt
open Ideal NumberField


namespace MetaMathlibExt


/--
[primeIdealValidCubicSymbol_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma primeIdealValidCubicSymbol_mem
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {P : Ideal (NumberField.RingOfIntegers K)}
  {a : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hPprime : P.IsPrime)
  (hPbot : P ≠ ⊥)
  (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3)
  (ha : a ∉ P) :
-- imply
  primeIdealValidCubicSymbol hZeta P a hPprime hPbot hNormCoprime ha ∈ ({(1 : NumberField.RingOfIntegers K), omega hZeta, omega hZeta ^ 2} : Set _) :=
-- proof
  (Classical.choose_spec
    (exists_cubic_root_eq_pow hZeta P a hPprime hPbot hNormCoprime ha)).1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[primeIdealValidCubicSymbol_spec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma primeIdealValidCubicSymbol_spec
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {P : Ideal (NumberField.RingOfIntegers K)}
  {a : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hPprime : P.IsPrime)
  (hPbot : P ≠ ⊥)
  (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3)
  (ha : a ∉ P) :
-- imply
  Ideal.Quotient.mk P (primeIdealValidCubicSymbol hZeta P a hPprime hPbot hNormCoprime ha) = Ideal.Quotient.mk P a ^ ((Ideal.absNorm P - 1) / 3) :=
-- proof
  (Classical.choose_spec
    (exists_cubic_root_eq_pow hZeta P a hPprime hPbot hNormCoprime ha)).2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[omegaQuotient_isPrimitiveRoot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma omegaQuotient_isPrimitiveRoot
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {P : Ideal (NumberField.RingOfIntegers K)}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hPprime : P.IsPrime)
  (hPbot : P ≠ ⊥)
  (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3) :
-- imply
  IsPrimitiveRoot (Ideal.Quotient.mk P (omega (K := K) hZeta)) 3 := by
-- proof
  have hNeBot : P ≠ ⊥ := hPbot
  have hAbsNeOne : Ideal.absNorm P ≠ 1 := by
    intro h
    have hTop : P = ⊤ := (Ideal.absNorm_eq_one_iff (I := P)).mp h
    exact hPprime.ne_top hTop
  have _ : P ≠ ⊥ := hNeBot
  exact hZeta.toInteger_isPrimitiveRoot.idealQuotient_mk hAbsNeOne hNormCoprime

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mk_one_ne_mk_omega](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma mk_one_ne_mk_omega
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {P : Ideal (NumberField.RingOfIntegers K)}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hPprime : P.IsPrime)
  (hPbot : P ≠ ⊥)
  (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3) :
-- imply
  Ideal.Quotient.mk P (1 : NumberField.RingOfIntegers K) ≠ Ideal.Quotient.mk P (omega (K := K) hZeta) := by
-- proof
  intro hEq
  have hPrim :=
    omegaQuotient_isPrimitiveRoot (K := K) hZeta P hPprime hPbot hNormCoprime
  have hOne : Ideal.Quotient.mk P (omega (K := K) hZeta) = 1 := by
    rw [← hEq, map_one]
  exact hPrim.ne_one (by norm_num) hOne

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mk_one_ne_mk_omega_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma mk_one_ne_mk_omega_sq
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {P : Ideal (NumberField.RingOfIntegers K)}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hPprime : P.IsPrime)
  (hPbot : P ≠ ⊥)
  (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3) :
-- imply
  Ideal.Quotient.mk P (1 : NumberField.RingOfIntegers K) ≠ Ideal.Quotient.mk P (omega (K := K) hZeta ^ 2) := by
-- proof
  intro hEq
  have hPrim :=
    omegaQuotient_isPrimitiveRoot (K := K) hZeta P hPprime hPbot hNormCoprime
  have hPow2 :
      (Ideal.Quotient.mk P (omega (K := K) hZeta)) ^ 2 = 1 := by
    rw [← map_pow, ← hEq, map_one]
  have hNe :
      (Ideal.Quotient.mk P (omega (K := K) hZeta)) ^ 2 ≠ 1 :=
    hPrim.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  exact hNe hPow2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mk_omega_ne_mk_omega_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma mk_omega_ne_mk_omega_sq
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {P : Ideal (NumberField.RingOfIntegers K)}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hPprime : P.IsPrime)
  (hPbot : P ≠ ⊥)
  (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3) :
-- imply
  Ideal.Quotient.mk P (omega (K := K) hZeta) ≠ Ideal.Quotient.mk P (omega (K := K) hZeta ^ 2) := by
-- proof
  intro hEq
  have hPrim :=
    omegaQuotient_isPrimitiveRoot (K := K) hZeta P hPprime hPbot hNormCoprime
  have hMkNeZero :
      Ideal.Quotient.mk P (omega (K := K) hZeta) ≠ 0 := by
    intro hZero
    have hpow : (Ideal.Quotient.mk P (omega (K := K) hZeta)) ^ 3 = 1 :=
      hPrim.pow_eq_one
    have : (0 : NumberField.RingOfIntegers K ⧸ P) ^ (3 : ℕ) = 1 := by
      rw [← hZero, hpow]
    simp at this
  have hPowEq :
      Ideal.Quotient.mk P (omega (K := K) hZeta) =
        Ideal.Quotient.mk P (omega (K := K) hZeta) ^ 2 := by
    rw [← map_pow, hEq]
  have hIsMax : P.IsMaximal := Ideal.IsPrime.isMaximal hPprime hPbot
  let _ : Field (NumberField.RingOfIntegers K ⧸ P) :=
    Ideal.Quotient.field P
  have hMul :
      Ideal.Quotient.mk P (omega (K := K) hZeta) *
        (1 - Ideal.Quotient.mk P (omega (K := K) hZeta)) = 0 := by
    have hSub :
        Ideal.Quotient.mk P (omega (K := K) hZeta) -
          Ideal.Quotient.mk P (omega (K := K) hZeta) ^ 2 = 0 := by
      rw [← hPowEq, sub_self]
    have h1 :
        Ideal.Quotient.mk P (omega (K := K) hZeta) *
            (1 - Ideal.Quotient.mk P (omega (K := K) hZeta)) =
          Ideal.Quotient.mk P (omega (K := K) hZeta) -
            Ideal.Quotient.mk P (omega (K := K) hZeta) ^ 2 := by
      ring
    rw [h1, hSub]
  rcases mul_eq_zero.mp hMul with hZero | hOne
  · exact hMkNeZero hZero
  · have hEqOne :
        Ideal.Quotient.mk P (omega (K := K) hZeta) = 1 := by
      have hSubZero :
          1 - Ideal.Quotient.mk P (omega (K := K) hZeta) = 0 := hOne
      have h2 :
          Ideal.Quotient.mk P (omega (K := K) hZeta) =
            1 - (1 - Ideal.Quotient.mk P (omega (K := K) hZeta)) := by
        ring
      rw [h2, hSubZero, sub_zero]
    exact hPrim.ne_one (by norm_num) hEqOne

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cubicRoot_quotient_pairwise_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma cubicRoot_quotient_pairwise_distinct
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {P : Ideal (NumberField.RingOfIntegers K)}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hPprime : P.IsPrime)
  (hPbot : P ≠ ⊥)
  (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3) :
-- imply
  Ideal.Quotient.mk P (1 : NumberField.RingOfIntegers K) ≠ Ideal.Quotient.mk P (omega (K := K) hZeta) ∧ Ideal.Quotient.mk P (1 : NumberField.RingOfIntegers K) ≠ Ideal.Quotient.mk P (omega (K := K) hZeta ^ 2) ∧ Ideal.Quotient.mk P (omega (K := K) hZeta) ≠ Ideal.Quotient.mk P (omega (K := K) hZeta ^ 2) :=
-- proof
  ⟨mk_one_ne_mk_omega hZeta P hPprime hPbot hNormCoprime,
    mk_one_ne_mk_omega_sq hZeta P hPprime hPbot hNormCoprime,
    mk_omega_ne_mk_omega_sq hZeta P hPprime hPbot hNormCoprime⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[primeIdealValidCubicSymbol_unique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma primeIdealValidCubicSymbol_unique
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {P : Ideal (NumberField.RingOfIntegers K)}
  {a c : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hPprime : P.IsPrime)
  (hPbot : P ≠ ⊥)
  (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3)
  (ha : a ∉ P)
  (hcMem : c ∈ ({(1 : NumberField.RingOfIntegers K), omega hZeta, omega hZeta ^ 2} : Set _))
  (hcSpec : Ideal.Quotient.mk P c = Ideal.Quotient.mk P a ^ ((Ideal.absNorm P - 1) / 3)) :
-- imply
  c = primeIdealValidCubicSymbol hZeta P a hPprime hPbot hNormCoprime ha := by
-- proof
  have hValidMem :=
    primeIdealValidCubicSymbol_mem hZeta P a hPprime hPbot hNormCoprime ha
  have hValidSpec :=
    primeIdealValidCubicSymbol_spec hZeta P a hPprime hPbot hNormCoprime ha
  have hEq :
      Ideal.Quotient.mk P c =
        Ideal.Quotient.mk P
          (primeIdealValidCubicSymbol hZeta P a hPprime hPbot
            hNormCoprime ha) := by
    rw [hcSpec, hValidSpec]
  have hPair :=
    cubicRoot_quotient_pairwise_distinct (K := K) hZeta P hPprime hPbot
      hNormCoprime
  have h1neW := hPair.1
  have h1neW2 := hPair.2.1
  have hWneW2 := hPair.2.2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcMem hValidMem
  rcases hcMem with rfl | rfl | rfl
  · rcases hValidMem with hV | hV | hV
    · exact hV.symm
    · exfalso
      have :
          Ideal.Quotient.mk P (1 : NumberField.RingOfIntegers K) =
            Ideal.Quotient.mk P (omega (K := K) hZeta) := by
        rw [hEq, hV]
      exact h1neW this
    · exfalso
      have :
          Ideal.Quotient.mk P (1 : NumberField.RingOfIntegers K) =
            Ideal.Quotient.mk P (omega (K := K) hZeta ^ 2) := by
        rw [hEq, hV]
      exact h1neW2 this
  · rcases hValidMem with hV | hV | hV
    · exfalso
      have :
          Ideal.Quotient.mk P (omega (K := K) hZeta) =
            Ideal.Quotient.mk P (1 : NumberField.RingOfIntegers K) := by
        rw [hEq, hV]
      exact h1neW this.symm
    · exact hV.symm
    · exfalso
      have :
          Ideal.Quotient.mk P (omega (K := K) hZeta) =
            Ideal.Quotient.mk P (omega (K := K) hZeta ^ 2) := by
        rw [hEq, hV]
      exact hWneW2 this
  · rcases hValidMem with hV | hV | hV
    · exfalso
      have :
          Ideal.Quotient.mk P (omega (K := K) hZeta ^ 2) =
            Ideal.Quotient.mk P (1 : NumberField.RingOfIntegers K) := by
        rw [hEq, hV]
      exact h1neW2 this.symm
    · exfalso
      have :
          Ideal.Quotient.mk P (omega (K := K) hZeta ^ 2) =
            Ideal.Quotient.mk P (omega (K := K) hZeta) := by
        rw [hEq, hV]
      exact hWneW2 this.symm
    · exact hV.symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[primeIdealValidCubicSymbol_characterization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma primeIdealValidCubicSymbol_characterization
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {P : Ideal (NumberField.RingOfIntegers K)}
  {a c : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hPprime : P.IsPrime)
  (hPbot : P ≠ ⊥)
  (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3)
  (ha : a ∉ P) :
-- imply
  (c = primeIdealValidCubicSymbol hZeta P a hPprime hPbot hNormCoprime ha ↔ c ∈ ({(1 : NumberField.RingOfIntegers K), omega hZeta, omega hZeta ^ 2} : Set _) ∧ Ideal.Quotient.mk P c = Ideal.Quotient.mk P a ^ ((Ideal.absNorm P - 1) / 3)) := by
-- proof
  constructor
  · intro hEq
    rw [hEq]
    exact ⟨primeIdealValidCubicSymbol_mem hZeta P a hPprime hPbot hNormCoprime ha,
      primeIdealValidCubicSymbol_spec hZeta P a hPprime hPbot hNormCoprime ha⟩
  · intro ⟨hMem, hSpec⟩
    exact primeIdealValidCubicSymbol_unique hZeta P a hPprime hPbot
      hNormCoprime ha c hMem hSpec

open Classical in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[primeIdealCubicSymbolFactorRaw_of_not_isPrime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma primeIdealCubicSymbolFactorRaw_of_not_isPrime
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {P : Ideal (NumberField.RingOfIntegers K)}
  {a : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hNotPrime : ¬ P.IsPrime) :
-- imply
  primeIdealCubicSymbolFactorRaw hZeta P a = 1 := by
-- proof
  simp [primeIdealCubicSymbolFactorRaw, hNotPrime]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[primeIdealCubicSymbolFactorRaw_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma primeIdealCubicSymbolFactorRaw_bot
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {a : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3) :
-- imply
  primeIdealCubicSymbolFactorRaw hZeta (⊥ : Ideal (NumberField.RingOfIntegers K)) a = 1 := by
-- proof
  simp [primeIdealCubicSymbolFactorRaw]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[primeIdealCubicSymbolFactorRaw_of_not_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma primeIdealCubicSymbolFactorRaw_of_not_coprime
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {P : Ideal (NumberField.RingOfIntegers K)}
  {a : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hPprime : P.IsPrime)
  (hPbot : P ≠ ⊥)
  (hNotCop : ¬ Nat.Coprime (Ideal.absNorm P) 3) :
-- imply
  primeIdealCubicSymbolFactorRaw hZeta P a = 1 := by
-- proof
  simp [primeIdealCubicSymbolFactorRaw, hPprime, hPbot, hNotCop]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[primeIdealCubicSymbolFactorRaw_eq_one_of_isPrime_of_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma primeIdealCubicSymbolFactorRaw_eq_one_of_isPrime_of_bot
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {P : Ideal (NumberField.RingOfIntegers K)}
  {a : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hPprime : P.IsPrime)
  (hBot : P = ⊥) :
-- imply
  primeIdealCubicSymbolFactorRaw hZeta P a = 1 := by
-- proof
  have hNotBot : ¬ (P ≠ ⊥) := by rw [hBot]; simp
  simp [primeIdealCubicSymbolFactorRaw, hPprime, hNotBot]

open Classical in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cubicResidueSymbolRaw_unit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma cubicResidueSymbolRaw_unit
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {a u : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hu : IsUnit u) :
-- imply
  cubicResidueSymbolRaw hZeta a u = 1 := by
-- proof
  unfold cubicResidueSymbolRaw
  have hu0 : u ≠ 0 := IsUnit.ne_zero hu
  simp only [hu0, ↓reduceIte]
  have hSpanTop :
      Ideal.span ({u} : Set (NumberField.RingOfIntegers K)) = ⊤ :=
    Ideal.span_singleton_eq_top.mpr hu
  have hIsUnitIdeal :
      IsUnit (Ideal.span ({u} : Set (NumberField.RingOfIntegers K))) := by
    rw [Ideal.isUnit_iff, hSpanTop]
  have hFacs :
      UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({u} : Set _)) = 0 := by
    exact UniqueFactorizationMonoid.normalizedFactors_of_isUnit hIsUnitIdeal
  simp [hFacs]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cubicResidueSymbolRaw_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma cubicResidueSymbolRaw_mul
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {a m n : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hm : m ≠ 0)
  (hn : n ≠ 0) :
-- imply
  cubicResidueSymbolRaw hZeta a (m * n) = cubicResidueSymbolRaw hZeta a m * cubicResidueSymbolRaw hZeta a n := by
-- proof
  unfold cubicResidueSymbolRaw
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  simp only [hm, hn, hmn, ↓reduceIte]
  have hSpanMul :
      Ideal.span ({m * n} : Set (NumberField.RingOfIntegers K)) =
        Ideal.span ({m} : Set _) * Ideal.span ({n} : Set _) := by
    rw [Ideal.span_singleton_mul_span_singleton]
  have hmBot :
      Ideal.span ({m} : Set (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hm
  have hnBot :
      Ideal.span ({n} : Set (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hn
  have hFacMul :
      UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({m * n} : Set _)) =
        UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({m} : Set _)) +
          UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({n} : Set _)) := by
    rw [hSpanMul]
    exact UniqueFactorizationMonoid.normalizedFactors_mul hmBot hnBot
  simp only [hFacMul, Multiset.map_add, Multiset.prod_add]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cubicResidueSymbolRaw_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma cubicResidueSymbolRaw_prime
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {a p : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hpPrime : Prime p)
  (hpNeZero : p ≠ 0) :
-- imply
  cubicResidueSymbolRaw hZeta a p = primeIdealCubicSymbolFactorRaw hZeta (Ideal.span {p}) a := by
-- proof
  unfold cubicResidueSymbolRaw
  simp only [hpNeZero, ↓reduceIte]
  have hSpanPrime :
      (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hpPrime
  have hSpanNeBot :
      Ideal.span ({p} : Set (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hpNeZero
  have hPrimeIdeal :
      Prime (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))) :=
    Ideal.prime_of_isPrime hSpanNeBot hSpanPrime
  have hIrred :
      Irreducible (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))) :=
    hPrimeIdeal.irreducible
  have hFac :
      UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({p} : Set _)) = {Ideal.span {p}} := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hIrred,
      normalize_eq]
  simp [hFac]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cubicResidueSymbolRaw_prime_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma cubicResidueSymbolRaw_prime_dvd
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {a p : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hpPrime : Prime p)
  (hpNeZero : p ≠ 0)
  (hNormCop : Nat.Coprime (Ideal.absNorm (Ideal.span ({p} : Set (NumberField.RingOfIntegers K)))) 3)
  (hdvd : p ∣ a) :
-- imply
  cubicResidueSymbolRaw hZeta a p = 0 := by
-- proof
  rw [cubicResidueSymbolRaw_prime hZeta a p hpPrime hpNeZero]
  have hSpanPrime :
      (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hpPrime
  have hSpanNeBot :
      Ideal.span ({p} : Set (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hpNeZero
  have hMem :
      a ∈ Ideal.span ({p} : Set (NumberField.RingOfIntegers K)) :=
    Ideal.mem_span_singleton.mpr hdvd
  simp only [primeIdealCubicSymbolFactorRaw,
    dite_eq_left hSpanPrime, dite_eq_left hSpanNeBot, dite_eq_left hNormCop, dite_eq_left hMem]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cubicResidueSymbolRaw_prime_not_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma cubicResidueSymbolRaw_prime_not_dvd
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {a p : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hpPrime : Prime p)
  (hpNeZero : p ≠ 0)
  (hNormCop : Nat.Coprime (Ideal.absNorm (Ideal.span ({p} : Set (NumberField.RingOfIntegers K)))) 3)
  (hndvd : ¬ p ∣ a) :
-- imply
  cubicResidueSymbolRaw hZeta a p ∈ ({(1 : NumberField.RingOfIntegers K), omega hZeta, omega hZeta ^ 2} : Set _) ∧ Ideal.Quotient.mk (Ideal.span {p}) (cubicResidueSymbolRaw hZeta a p) = Ideal.Quotient.mk (Ideal.span {p}) a ^ ((Ideal.absNorm (Ideal.span {p}) - 1) / 3) := by
-- proof
  have hNotMem :
      a ∉ Ideal.span ({p} : Set (NumberField.RingOfIntegers K)) := by
    rwa [Ideal.mem_span_singleton]
  rw [cubicResidueSymbolRaw_prime hZeta a p hpPrime hpNeZero]
  have hSpanPrime :
      (Ideal.span ({p} : Set (NumberField.RingOfIntegers K))).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hpPrime
  have hSpanNeBot :
      Ideal.span ({p} : Set (NumberField.RingOfIntegers K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hpNeZero
  have hEq :
      primeIdealCubicSymbolFactorRaw hZeta (Ideal.span {p}) a =
        primeIdealValidCubicSymbol hZeta (Ideal.span {p}) a
          hSpanPrime hSpanNeBot hNormCop hNotMem := by
    simp only [primeIdealCubicSymbolFactorRaw,
      dite_eq_left hSpanPrime, dite_eq_left hSpanNeBot, dite_eq_left hNormCop,
      dite_eq_right hNotMem]
  rw [hEq]
  constructor
  · exact primeIdealValidCubicSymbol_mem hZeta _ _
      hSpanPrime hSpanNeBot hNormCop hNotMem
  · exact primeIdealValidCubicSymbol_spec hZeta _ _
      hSpanPrime hSpanNeBot hNormCop hNotMem

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cubicResidueSymbol_unit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma cubicResidueSymbol_unit
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {a u : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hu : IsUnit u)
  (hValid : IsCubicResidueDenominator u) :
-- imply
  cubicResidueSymbol hZeta a u hValid = 1 := by
-- proof
  simpa [cubicResidueSymbol] using cubicResidueSymbolRaw_unit hZeta a u hu

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cubicResidueSymbol_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma cubicResidueSymbol_mul
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {a m n : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hmValid : IsCubicResidueDenominator m)
  (hnValid : IsCubicResidueDenominator n)
  (hmnValid : IsCubicResidueDenominator (m * n)) :
-- imply
  cubicResidueSymbol hZeta a (m * n) hmnValid = cubicResidueSymbol hZeta a m hmValid * cubicResidueSymbol hZeta a n hnValid := by
-- proof
  simpa [cubicResidueSymbol] using
    cubicResidueSymbolRaw_mul hZeta a m n hmValid.1 hnValid.1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cubicResidueSymbol_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma cubicResidueSymbol_prime
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {a p : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hpPrime : Prime p)
  (hpValid : IsCubicResidueDenominator p) :
-- imply
  cubicResidueSymbol hZeta a p hpValid = primeIdealCubicSymbol hZeta (Ideal.span {p}) a (Ideal.isPrime_span_singleton_of_prime hpPrime) (by simpa [Ne, Ideal.span_singleton_eq_bot] using hpValid.1) hpValid.2 := by
-- proof
  simpa [cubicResidueSymbol, primeIdealCubicSymbol] using
    cubicResidueSymbolRaw_prime hZeta a p hpPrime hpValid.1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cubicResidueSymbol_prime_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma cubicResidueSymbol_prime_dvd
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {a p : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hpPrime : Prime p)
  (hpValid : IsCubicResidueDenominator p)
  (hdvd : p ∣ a) :
-- imply
  cubicResidueSymbol hZeta a p hpValid = 0 := by
-- proof
  simpa [cubicResidueSymbol] using
    cubicResidueSymbolRaw_prime_dvd
      hZeta a p hpPrime hpValid.1 hpValid.2 hdvd

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cubicResidueSymbol_prime_not_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
lemma cubicResidueSymbol_prime_not_dvd
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {a p : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hpPrime : Prime p)
  (hpValid : IsCubicResidueDenominator p)
  (hndvd : ¬ p ∣ a) :
-- imply
  cubicResidueSymbol hZeta a p hpValid ∈ ({(1 : NumberField.RingOfIntegers K), omega hZeta, omega hZeta ^ 2} : Set _) ∧ Ideal.Quotient.mk (Ideal.span {p}) (cubicResidueSymbol hZeta a p hpValid) = Ideal.Quotient.mk (Ideal.span {p}) a ^ ((Ideal.absNorm (Ideal.span {p}) - 1) / 3) := by
-- proof
  simpa [cubicResidueSymbol] using
    cubicResidueSymbolRaw_prime_not_dvd
      hZeta a p hpPrime hpValid.1 hpValid.2 hndvd

end MetaMathlibExt

/--
[exists_cubic_root_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean)
-/
@[path]
private lemma exists_cubic_root_eq_pow_eq
  [Field K]
  [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]
  {zeta : K}
  {P : Ideal (NumberField.RingOfIntegers K)}
  {a : NumberField.RingOfIntegers K}
-- given
  (hZeta : IsPrimitiveRoot zeta 3)
  (hPprime : P.IsPrime)
  (hPbot : P ≠ ⊥)
  (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3)
  (ha : a ∉ P) :
-- imply
  ∃ c : NumberField.RingOfIntegers K, c ∈ ({(1 : NumberField.RingOfIntegers K), omega hZeta, omega hZeta ^ 2} : Set _) ∧ Ideal.Quotient.mk P c = Ideal.Quotient.mk P a ^ ((Ideal.absNorm P - 1) / 3) := by
-- proof
  apply MetaMathlibExt.exists_cubic_root_eq_pow hZeta P a hPprime hPbot hNormCoprime ha


-- created on 2026-10-23

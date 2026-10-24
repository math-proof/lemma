/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean -/

import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.NumberField.Ideal.Basic

namespace MetaMathlibExt

open Ideal NumberField

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]

/-
Source: Peng Gao and Liangyi Zhao, "Ratios conjecture of cubic L-functions of prime
moduli," arXiv:2311.08626v3, Indagationes Mathematicae. Definition of cubic residue
symbol leg {·}{·}_3 for K = Q(ω), O_K = Z[ω], ω = hZeta.toInteger.
Bytes [25829,26379) of RatioconjcubicHeckeLfcnsPrim_031.tex.
-/

abbrev omega {zeta : K} (hZeta : IsPrimitiveRoot zeta 3) :
    NumberField.RingOfIntegers K :=
  hZeta.toInteger

omit [IsCyclotomicExtension {3} ℚ K] in
lemma exists_cubic_root_eq_pow
    {zeta : K} [IsCyclotomicExtension {3} ℚ K]
    (hZeta : IsPrimitiveRoot zeta 3)
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K)
    (hPprime : P.IsPrime)
    (hPbot : P ≠ ⊥)
    (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3)
    (ha : a ∉ P) :
    ∃ c : NumberField.RingOfIntegers K,
      c ∈ ({(1 : NumberField.RingOfIntegers K),
        omega hZeta, omega hZeta ^ 2} : Set _) ∧
      Ideal.Quotient.mk P c =
        Ideal.Quotient.mk P a ^ ((Ideal.absNorm P - 1) / 3) := by
  classical
  have : P.IsMaximal := Ideal.IsPrime.isMaximal hPprime hPbot
  let _ : Field (NumberField.RingOfIntegers K ⧸ P) :=
    Ideal.Quotient.field P
  have : Finite (NumberField.RingOfIntegers K ⧸ P) :=
    Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne P)
  let _ : Fintype (NumberField.RingOfIntegers K ⧸ P) :=
    Fintype.ofFinite _
  have hAbsNeOne : Ideal.absNorm P ≠ 1 := by
    intro h
    have hTop : P = ⊤ := (Ideal.absNorm_eq_one_iff (I := P)).mp h
    exact hPprime.ne_top hTop
  have hCoprime : Nat.Coprime (Ideal.absNorm P) 3 := hNormCoprime
  have hPrim : IsPrimitiveRoot
      (Ideal.Quotient.mk P (omega (K := K) hZeta)) 3 :=
    hZeta.toInteger_isPrimitiveRoot.idealQuotient_mk hAbsNeOne hCoprime
  have hCardEq :
      Fintype.card (NumberField.RingOfIntegers K ⧸ P) =
        Ideal.absNorm P := by
    calc Fintype.card (NumberField.RingOfIntegers K ⧸ P)
        = Nat.card (NumberField.RingOfIntegers K ⧸ P) :=
          Fintype.card_eq_nat_card
      _ = Submodule.cardQuot P := (Submodule.cardQuot_apply (S := P)).symm
      _ = Ideal.absNorm P := (Ideal.absNorm_apply (I := P)).symm
  have hMkOmegaNeZero : Ideal.Quotient.mk P (omega hZeta) ≠ 0 := by
    intro hEq
    have hMem : (omega hZeta) ∈ P :=
      (Ideal.Quotient.eq_zero_iff_mem).mp hEq
    have hpow1 : (Ideal.Quotient.mk P (omega hZeta)) ^ 3 = 1 :=
      hPrim.pow_eq_one
    have : (0 : NumberField.RingOfIntegers K ⧸ P) ^ (3 : ℕ) = 1 := by
      rw [← hEq, hpow1]
    simp at this
  have hMkANeZero : Ideal.Quotient.mk P a ≠ 0 := by
    intro hEq
    rw [Ideal.Quotient.eq_zero_iff_mem] at hEq
    exact ha hEq
  have hPowCardOmega :
      (Ideal.Quotient.mk P (omega hZeta)) ^
        (Fintype.card (NumberField.RingOfIntegers K ⧸ P) - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one
      (Ideal.Quotient.mk P (omega hZeta)) hMkOmegaNeZero
  have hDvd :
      3 ∣ Fintype.card (NumberField.RingOfIntegers K ⧸ P) - 1 :=
    hPrim.dvd_of_pow_eq_one _ hPowCardOmega
  rw [hCardEq] at hDvd
  have hPowA :
      (Ideal.Quotient.mk P a) ^
        (Fintype.card (NumberField.RingOfIntegers K ⧸ P) - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one
      (Ideal.Quotient.mk P a) hMkANeZero
  rw [hCardEq] at hPowA
  have hThreeDvd : 3 ∣ Ideal.absNorm P - 1 := hDvd
  have hExp :
      3 * ((Ideal.absNorm P - 1) / 3) = Ideal.absNorm P - 1 :=
    Nat.mul_div_cancel' hThreeDvd
  have hEulerCube :
      (Ideal.Quotient.mk P a ^ ((Ideal.absNorm P - 1) / 3)) ^ 3 = 1 := by
    calc (Ideal.Quotient.mk P a ^ ((Ideal.absNorm P - 1) / 3)) ^ 3
        = (Ideal.Quotient.mk P a) ^
            (((Ideal.absNorm P - 1) / 3) * 3) := by rw [← pow_mul]
      _ = (Ideal.Quotient.mk P a) ^ (3 * ((Ideal.absNorm P - 1) / 3)) := by
          rw [Nat.mul_comm]
      _ = (Ideal.Quotient.mk P a) ^ (Ideal.absNorm P - 1) := by rw [hExp]
      _ = 1 := hPowA
  obtain ⟨b, hb⟩ :=
    Ideal.Quotient.mk_surjective
      (I := P) (Ideal.Quotient.mk P a ^ ((Ideal.absNorm P - 1) / 3))
  have hbCube : Ideal.Quotient.mk P (b ^ 3 - 1) = 0 := by
    rw [map_sub, map_pow, hb, map_one, sub_eq_zero.mpr hEulerCube]
  have hCubeEq :
      b ^ 3 - 1 = (b - 1) * (b - omega hZeta) * (b - omega hZeta ^ 2) :=
    IsCyclotomicExtension.Rat.Three.cube_sub_one_eq_mul hZeta b
  have hMkProdZero :
      Ideal.Quotient.mk P ((b - 1) * (b - omega hZeta) *
        (b - omega hZeta ^ 2)) = 0 := by
    rw [← hCubeEq, hbCube]
  rw [map_mul, map_mul] at hMkProdZero
  have hOr :
      Ideal.Quotient.mk P (b - 1) = 0 ∨
        Ideal.Quotient.mk P (b - omega hZeta) = 0 ∨
          Ideal.Quotient.mk P (b - omega hZeta ^ 2) = 0 := by
    have h1 :
        Ideal.Quotient.mk P (b - 1) *
            Ideal.Quotient.mk P (b - omega hZeta) *
              Ideal.Quotient.mk P (b - omega hZeta ^ 2) = 0 := hMkProdZero
    rcases mul_eq_zero.mp h1 with h12 | h3
    · rcases mul_eq_zero.mp h12 with h1' | h2'
      · left; exact h1'
      · right; left; exact h2'
    · right; right; exact h3
  rcases hOr with h1 | h2 | h3
  · refine ⟨1, by simp, ?_⟩
    have hmk1 : Ideal.Quotient.mk P (b - 1) = 0 := h1
    rw [map_sub, sub_eq_zero] at hmk1
    rw [← hb, hmk1]
  · refine ⟨omega hZeta, by simp, ?_⟩
    have hmk2 : Ideal.Quotient.mk P (b - omega hZeta) = 0 := h2
    rw [map_sub, sub_eq_zero] at hmk2
    rw [← hb, hmk2]
  · refine ⟨omega hZeta ^ 2, by simp, ?_⟩
    have hmk3 : Ideal.Quotient.mk P (b - omega hZeta ^ 2) = 0 := h3
    rw [map_sub, sub_eq_zero] at hmk3
    rw [← hb, hmk3]

open Classical in
noncomputable def primeIdealValidCubicSymbol
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K)
    (hPprime : P.IsPrime)
    (hPbot : P ≠ ⊥)
    (hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3)
    (ha : a ∉ P) : NumberField.RingOfIntegers K :=
  Classical.choose
    (exists_cubic_root_eq_pow hZeta P a hPprime hPbot hNormCoprime ha)

open Classical in
/-- Implementation detail: totalizes the prime-ideal symbol, returning `1` outside
the source domain (nonprime `P`, `P = ⊥`, or norm not coprime to `3`). Prefer
`primeIdealCubicSymbol`. -/
noncomputable def primeIdealCubicSymbolFactorRaw
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K) : NumberField.RingOfIntegers K :=
  if hPprime : P.IsPrime then
    if hPbot : P ≠ ⊥ then
      if hCop : Nat.Coprime (Ideal.absNorm P) 3 then
        if ha : a ∈ P then 0
        else primeIdealValidCubicSymbol hZeta P a hPprime hPbot hCop ha
      else 1
    else 1
  else 1

open Classical in
/-- Implementation detail: totalizes zero denominators to `0` and ignores
out-of-domain prime factors via the raw factor. Prefer `cubicResidueSymbol`
with `IsCubicResidueDenominator`. -/
noncomputable def cubicResidueSymbolRaw
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (a n : NumberField.RingOfIntegers K) : NumberField.RingOfIntegers K :=
  if n = 0 then 0
  else
    let I := Ideal.span ({n} : Set (NumberField.RingOfIntegers K))
    let facs := UniqueFactorizationMonoid.normalizedFactors I
    (facs.map (fun P => primeIdealCubicSymbolFactorRaw hZeta P a)).prod

/-- The cubic residue symbol of `a` at a prime ideal in the source domain. -/
noncomputable def primeIdealCubicSymbol
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (P : Ideal (NumberField.RingOfIntegers K))
    (a : NumberField.RingOfIntegers K)
    (_hPprime : P.IsPrime)
    (_hPbot : P ≠ ⊥)
    (_hNormCoprime : Nat.Coprime (Ideal.absNorm P) 3) :
    NumberField.RingOfIntegers K :=
  primeIdealCubicSymbolFactorRaw hZeta P a

/-- A nonzero denominator whose principal-ideal norm is coprime to `3`. -/
def IsCubicResidueDenominator
    (n : NumberField.RingOfIntegers K) : Prop :=
  n ≠ 0 ∧ Nat.Coprime (Ideal.absNorm (Ideal.span {n})) 3

/-- The cubic residue symbol of `a` modulo a denominator in the source domain. -/
noncomputable def cubicResidueSymbol
    {zeta : K}
    (hZeta : IsPrimitiveRoot zeta 3)
    (a n : NumberField.RingOfIntegers K)
    (_hValid : IsCubicResidueDenominator n) :
    NumberField.RingOfIntegers K :=
  cubicResidueSymbolRaw hZeta a n
end MetaMathlibExt

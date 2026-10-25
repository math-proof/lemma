/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean -/

import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Theorem.NumberTheory.Cyclotomic.CubicResidueSymbol


namespace MetaMathlibExt

open Ideal NumberField

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]

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

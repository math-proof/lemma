import Mathlib.Analysis.SpecificLimits.Basic
open scoped BigOperators

/-!
# Takagi function on dyadic rationals

Formalizes Definition `takagi_newdef` (source statement `jis_23b2f8f9e624bca533bd6deb`,
concept `jis_sem_95dbf183cc4eaf1172157db5`): binary digits, the `ell` coefficients,
and the Takagi sum over dyadic presentations `n / 2 ^ (k + 1)`.
-/


namespace MetaMathlibExt

/-- Binary digit `nᵢ` of `n` (required clause `bit`): `Nat.testBit n i` as `1` or `0`
for nonnegative integer indices `i`, and `0` for negative `i`.
Cites concept `jis_sem_95dbf183cc4eaf1172157db5` and source statement
`jis_23b2f8f9e624bca533bd6deb`. -/
def takagiBit (n : Nat) (i : Int) : Nat :=
  if 0 ≤ i then (if Nat.testBit n i.toNat then 1 else 0) else 0

/-- Coefficient `ell` (required clause `ell`): `ell_1 = 0`, and `ell_(i+1)` is the
prefix-digit sum below `k - i` when that digit is `0`, else `i` minus that sum.
Cites concept `jis_sem_95dbf183cc4eaf1172157db5` and source statement
`jis_23b2f8f9e624bca533bd6deb`. -/
def takagiEll (n : Nat) (k : Int) : Nat → Nat
  | 0 => 0
  | (i + 1) =>
    if takagiBit n (k - (i : Int)) = 0 then
      ∑ j ∈ Finset.range i, takagiBit n (k - (j : Int))
    else i - ∑ j ∈ Finset.range i, takagiBit n (k - (j : Int))

/-- Takagi function on the dyadic presentation `n / 2 ^ (k + 1)` (required clause
`takagi`): the infinite real sum of `ell_(i+1) / 2 ^ (i+1)` over `i : Nat`.
Cites concept `jis_sem_95dbf183cc4eaf1172157db5` and source statement
`jis_23b2f8f9e624bca533bd6deb`. -/
noncomputable def takagiNewdef (n : Nat) (k : Int) : Real :=
  ∑' i, (takagiEll n k (i + 1) : Real) / 2 ^ (i + 1)

end MetaMathlibExt

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

/-- Defining equation of `takagiBit` (required clause `bit`): unfolds by `rfl`.
Cites concept `jis_sem_95dbf183cc4eaf1172157db5` and source statement
`jis_23b2f8f9e624bca533bd6deb`. -/
theorem takagiBit_eq (n : Nat) (i : Int) :
    takagiBit n i =
      (if 0 ≤ i then (if Nat.testBit n i.toNat then 1 else 0) else 0) := rfl

/-- Defining equation of `takagiEll` at the padded index `0` (required clause `ell`):
the auxiliary base value `takagiEll n k 0` is `0`. This is not the source value
`ell_1`, which is `takagiEll n k 1` and is covered by `takagiEll_one`.
Cites concept `jis_sem_95dbf183cc4eaf1172157db5` and source statement
`jis_23b2f8f9e624bca533bd6deb`. -/
theorem takagiEll_zero (n : Nat) (k : Int) : takagiEll n k 0 = 0 := rfl

/-- Defining equation of `takagiEll` at successors (required clause `ell`):
unfolds by `rfl`.
Cites concept `jis_sem_95dbf183cc4eaf1172157db5` and source statement
`jis_23b2f8f9e624bca533bd6deb`. -/
theorem takagiEll_succ (n : Nat) (k : Int) (i : Nat) :
    takagiEll n k (i + 1) =
      (if takagiBit n (k - (i : Int)) = 0 then
        ∑ j ∈ Finset.range i, takagiBit n (k - (j : Int))
      else i - ∑ j ∈ Finset.range i, takagiBit n (k - (j : Int))) := rfl

/-- Defining equation of `takagiNewdef` (required clause `takagi`): unfolds by `rfl`.
Cites concept `jis_sem_95dbf183cc4eaf1172157db5` and source statement
`jis_23b2f8f9e624bca533bd6deb`. -/
theorem takagiNewdef_eq (n : Nat) (k : Int) :
    takagiNewdef n k =
      ∑' i, (takagiEll n k (i + 1) : Real) / 2 ^ (i + 1) := rfl

/-- Boundary lemma (required clause `bit`): digits at negative indices are `0`.
Cites concept `jis_sem_95dbf183cc4eaf1172157db5` and source statement
`jis_23b2f8f9e624bca533bd6deb`. -/
theorem takagiBit_neg (n : Nat) (i : Int) (h : i < 0) :
    takagiBit n i = 0 := by
  unfold takagiBit
  rw [ite_eq_right (not_le.mpr h)]

/-- Boundary lemma (required clause `ell`): `ell_1 = 0` for all presentations.
Cites concept `jis_sem_95dbf183cc4eaf1172157db5` and source statement
`jis_23b2f8f9e624bca533bd6deb`. -/
theorem takagiEll_one (n : Nat) (k : Int) : takagiEll n k 1 = 0 := by
  simp [takagiEll]

end MetaMathlibExt

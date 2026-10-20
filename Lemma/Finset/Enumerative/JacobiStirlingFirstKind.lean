import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.JacobiStirlingFirstKind
open scoped BigOperators
open MetaMathlibExt


/--
[jacobiStirlingFirst_initial_row](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/JacobiStirlingFirstKind.lean)
-/
@[path]
private lemma jacobiStirlingFirst_initial_row_eq
  [CommRing R]
  {k : ℕ}
  {ζ : R} :
-- imply
  jacobiStirlingFirst 0 k ζ = if k = 0 then 1 else 0 := by
-- proof
  apply MetaMathlibExt.jacobiStirlingFirst_initial_row k ζ

/--
[jacobiStirlingFirst_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/JacobiStirlingFirstKind.lean)
-/
@[path]
private lemma jacobiStirlingFirst_recurrence_eq
  [CommRing R]
  {n k : ℕ}
  {ζ : R} :
-- imply
  jacobiStirlingFirst (n + 1) (k + 1) ζ =
      jacobiStirlingFirst n k ζ -
        (n : R) * ((n : R) + ζ) * jacobiStirlingFirst n (k + 1) ζ := by
-- proof
  apply MetaMathlibExt.jacobiStirlingFirst_recurrence n k ζ

/--
[jacobiStirlingFirst_support](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/JacobiStirlingFirstKind.lean)
-/
@[path]
private lemma jacobiStirlingFirst_support_eq
  [CommRing R]
  {n k : ℕ}
  {ζ : R}
-- given
  (h : n < k) :
-- imply
  jacobiStirlingFirst n k ζ = 0 := by
-- proof
  apply MetaMathlibExt.jacobiStirlingFirst_support n k ζ h

/--
[jacobiStirlingFirst_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/JacobiStirlingFirstKind.lean)
-/
@[path]
private lemma jacobiStirlingFirst_diagonal_eq
  [CommRing R]
  {n : ℕ}
  {ζ : R} :
-- imply
  jacobiStirlingFirst n n ζ = 1 := by
-- proof
  apply MetaMathlibExt.jacobiStirlingFirst_diagonal n ζ


-- created on 2026-10-20

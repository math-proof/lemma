import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.JacobiStirlingFirstKind
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[jacobiStirlingFirst_initial_row](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/JacobiStirlingFirstKind.lean)
-/
@[path]
lemma jacobiStirlingFirst_initial_row
  [CommRing R]
  {k : ℕ}
  {ζ : R} :
-- imply
  jacobiStirlingFirst 0 k ζ = if k = 0 then 1 else 0 := by
-- proof
  unfold jacobiStirlingFirst jacobiStirlingFirstPoly
  simp [Polynomial.coeff_one]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[jacobiStirlingFirst_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/JacobiStirlingFirstKind.lean)
-/
@[path]
lemma jacobiStirlingFirst_recurrence
  [CommRing R]
  {n k : ℕ}
  {ζ : R} :
-- imply
  jacobiStirlingFirst (n + 1) (k + 1) ζ =
      jacobiStirlingFirst n k ζ -
        (n : R) * ((n : R) + ζ) * jacobiStirlingFirst n (k + 1) ζ := by
-- proof
  unfold jacobiStirlingFirst
  have hprod : jacobiStirlingFirstPoly (n + 1) ζ =
    jacobiStirlingFirstPoly n ζ *
      (Polynomial.X - Polynomial.C ((n : R) * ((n : R) + ζ))) := by
    unfold jacobiStirlingFirstPoly
    rw [Finset.prod_range_succ]
  rw [hprod, mul_sub, Polynomial.coeff_sub, Polynomial.coeff_mul_X,
    Polynomial.coeff_mul_C,
    mul_comm ((jacobiStirlingFirstPoly n ζ).coeff (k + 1)) _]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[jacobiStirlingFirst_support](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/JacobiStirlingFirstKind.lean)
-/
@[path]
lemma jacobiStirlingFirst_support
  [CommRing R]
  {n k : ℕ}
  {ζ : R}
-- given
  (h : n < k) :
-- imply
  jacobiStirlingFirst n k ζ = 0 := by
-- proof
  induction n generalizing k with
  | zero =>
    have hk : k ≠ 0 := by omega
    have h0 := jacobiStirlingFirst_initial_row k ζ
    rwa [ite_eq_right hk] at h0
  | succ n ih =>
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have h1 : n < m := by omega
    have h2 : n < m + 1 := by omega
    have e1 : jacobiStirlingFirst n m ζ = 0 := ih m h1
    have e2 : jacobiStirlingFirst n (m + 1) ζ = 0 := ih (m + 1) h2
    rw [jacobiStirlingFirst_recurrence, e1, e2, mul_zero, sub_self]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[jacobiStirlingFirst_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/JacobiStirlingFirstKind.lean)
-/
@[path]
lemma jacobiStirlingFirst_diagonal
  [CommRing R]
  {n : ℕ}
  {ζ : R} :
-- imply
  jacobiStirlingFirst n n ζ = 1 := by
-- proof
  induction n with
  | zero =>
    have h0 := jacobiStirlingFirst_initial_row 0 ζ
    rwa [ite_eq_left rfl] at h0
  | succ n ih =>
    rw [jacobiStirlingFirst_recurrence, ih,
      jacobiStirlingFirst_support n (n + 1) ζ (by omega), mul_zero, sub_zero]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26

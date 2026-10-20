import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.StaverIdentity
open MetaMathlibExt


/--
[staver_sign_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StaverIdentity.lean)
-/
@[path]
private lemma staver_sign_mul_eq
  {n k : ℕ}
-- given
  (hk : k ≤ n) :
-- imply
  (-1 : ℚ) ^ (n - k) * (-1 : ℚ) ^ k = (-1 : ℚ) ^ n := by
-- proof
  apply MetaMathlibExt.staver_sign_mul n k hk

/--
[staver_sign_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StaverIdentity.lean)
-/
@[path]
private lemma staver_sign_sq_eq
  {k : ℕ} :
-- imply
  (-1 : ℚ) ^ k * (-1 : ℚ) ^ k = 1 := by
-- proof
  apply MetaMathlibExt.staver_sign_sq k

/--
[staver_sign_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StaverIdentity.lean)
-/
@[path]
private lemma staver_sign_odd_eq
  {n k : ℕ}
-- given
  (hodd : Odd n)
  (hk : k ≤ n) :
-- imply
  (-1 : ℚ) ^ (n - k) = -(-1 : ℚ) ^ k := by
-- proof
  apply MetaMathlibExt.staver_sign_odd hodd hk

/--
[staver_sign_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StaverIdentity.lean)
-/
@[path]
private lemma staver_sign_even_eq
  {n k : ℕ}
-- given
  (heven : Even n)
  (hk : k ≤ n) :
-- imply
  (-1 : ℚ) ^ (n - k) = (-1 : ℚ) ^ k := by
-- proof
  apply MetaMathlibExt.staver_sign_even heven hk

/--
[staver_reflect_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StaverIdentity.lean)
-/
@[path]
private lemma staver_reflect_zero_eq
  {n : ℕ} :
-- imply
  (∑ k ∈ Finset.range (n + 1),
    (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹) =
    ∑ k ∈ Finset.range (n + 1),
    (-1 : ℚ) ^ k * ((Nat.choose n k : ℚ))⁻¹ := by
-- proof
  apply MetaMathlibExt.staver_reflect_zero n

/--
[staver_reflect_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StaverIdentity.lean)
-/
@[path]
private lemma staver_reflect_one_eq
  {n : ℕ} :
-- imply
  (∑ k ∈ Finset.range (n + 1),
    (-1 : ℚ) ^ (n - k) * (k : ℚ) * ((Nat.choose n k : ℚ))⁻¹) =
    ∑ k ∈ Finset.range (n + 1),
    (-1 : ℚ) ^ k * ((n - k : ℕ) : ℚ) * ((Nat.choose n k : ℚ))⁻¹ := by
-- proof
  apply MetaMathlibExt.staver_reflect_one n

/--
[staver_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StaverIdentity.lean)
-/
@[path]
private lemma staver_identity_eq
  {n : ℕ} :
-- imply
  (Even n →
    ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - k) * (k : ℚ) * ((Nat.choose n k : ℚ))⁻¹ =
    (n : ℚ) / 2 * ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹) ∧
    (Odd n →
    ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹ = 0) := by
-- proof
  apply MetaMathlibExt.staver_identity n


-- created on 2026-10-20

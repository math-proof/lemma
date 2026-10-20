import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.EulerPrime
open MetaMathlibExt


/--
[EulerianForm_perfect](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
private lemma EulerianForm_perfect_eq
  {N q k n : ℕ}
-- given
  (h : EulerianForm N q k n) :
-- imply
  Nat.Perfect N := by
-- proof
  apply MetaMathlibExt.EulerianForm_perfect h

/--
[EulerianForm_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
private lemma EulerianForm_odd_eq
  {N q k n : ℕ}
-- given
  (h : EulerianForm N q k n) :
-- imply
  Odd N := by
-- proof
  apply MetaMathlibExt.EulerianForm_odd h

/--
[EulerianForm_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
private lemma EulerianForm_prime_eq
  {N q k n : ℕ}
-- given
  (h : EulerianForm N q k n) :
-- imply
  Nat.Prime q := by
-- proof
  apply MetaMathlibExt.EulerianForm_prime h

/--
[EulerianForm_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
private lemma EulerianForm_eq_eq
  {N q k n : ℕ}
-- given
  (h : EulerianForm N q k n) :
-- imply
  N = q ^ k * n ^ 2 := by
-- proof
  apply MetaMathlibExt.EulerianForm_eq h

/--
[EulerianForm_mod4_q](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
private lemma EulerianForm_mod4_q_eq
  {N q k n : ℕ}
-- given
  (h : EulerianForm N q k n) :
-- imply
  q % 4 = 1 := by
-- proof
  apply MetaMathlibExt.EulerianForm_mod4_q h

/--
[EulerianForm_mod4_k](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
private lemma EulerianForm_mod4_k_eq
  {N q k n : ℕ}
-- given
  (h : EulerianForm N q k n) :
-- imply
  k % 4 = 1 := by
-- proof
  apply MetaMathlibExt.EulerianForm_mod4_k h

/--
[EulerianForm_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
private lemma EulerianForm_coprime_eq
  {N q k n : ℕ}
-- given
  (h : EulerianForm N q k n) :
-- imply
  Nat.Coprime q n := by
-- proof
  apply MetaMathlibExt.EulerianForm_coprime h

/--
[IsEulerPrime_intro](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
private lemma IsEulerPrime_intro_eq
  {N q k n : ℕ}
-- given
  (h : EulerianForm N q k n) :
-- imply
  IsEulerPrime N q := by
-- proof
  apply MetaMathlibExt.IsEulerPrime_intro h

/--
[IsEulerPrime_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
private lemma IsEulerPrime_iff_eq
  {N q : ℕ} :
-- imply
  IsEulerPrime N q ↔ ∃ k n, EulerianForm N q k n := by
-- proof
  apply MetaMathlibExt.IsEulerPrime_iff

/--
[IsEulerPrime_perfect](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
private lemma IsEulerPrime_perfect_eq
  {N q : ℕ}
-- given
  (h : IsEulerPrime N q) :
-- imply
  Nat.Perfect N := by
-- proof
  apply MetaMathlibExt.IsEulerPrime_perfect h

/--
[IsEulerPrime_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
private lemma IsEulerPrime_odd_eq
  {N q : ℕ}
-- given
  (h : IsEulerPrime N q) :
-- imply
  Odd N := by
-- proof
  apply MetaMathlibExt.IsEulerPrime_odd h

/--
[IsEulerPrime_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
private lemma IsEulerPrime_prime_eq
  {N q : ℕ}
-- given
  (h : IsEulerPrime N q) :
-- imply
  Nat.Prime q := by
-- proof
  apply MetaMathlibExt.IsEulerPrime_prime h

/--
[IsEulerPrime_factor_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
private lemma IsEulerPrime_factor_eq_eq
  {N q : ℕ}
-- given
  (h : IsEulerPrime N q) :
-- imply
  ∃ k n, N = q ^ k * n ^ 2 := by
-- proof
  apply MetaMathlibExt.IsEulerPrime_factor_eq h

/--
[IsEulerPrime_exists_factor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
private lemma IsEulerPrime_exists_factor_eq
  {N q : ℕ}
-- given
  (h : IsEulerPrime N q) :
-- imply
  ∃ k n, N = q ^ k * n ^ 2 ∧ q % 4 = 1 ∧ k % 4 = 1 ∧
    Nat.Coprime q n := by
-- proof
  apply MetaMathlibExt.IsEulerPrime_exists_factor h

/--
[euler_odd_perfect_form](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
private lemma euler_odd_perfect_form_eq
  {n : ℕ}
-- given
  (hodd : Odd n)
  (hperf : n.Perfect) :
-- imply
  ∃ q s m : ℕ,
    q.Prime ∧ n = q ^ s * m ^ 2 ∧ Nat.ModEq 4 q 1 ∧
    Nat.ModEq 4 s 1 ∧ q.Coprime m := by
-- proof
  apply MetaMathlibExt.euler_odd_perfect_form n hodd hperf


-- created on 2026-10-20

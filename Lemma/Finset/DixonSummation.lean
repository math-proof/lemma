import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.DixonSummation
open MetaMathlibExt


/--
[extFact_of_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma extFact_of_neg_eq
  {n : ℤ}
-- given
  (hn : n < 0) :
-- imply
  extFact n = 0 := by
-- proof
  apply MetaMathlibExt.extFact_of_neg hn

/--
[extFact_natCast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma extFact_natCast_eq
  {n : ℕ} :
-- imply
  extFact n = n.factorial := by
-- proof
  apply MetaMathlibExt.extFact_natCast n

/--
[invFact_of_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma invFact_of_neg_eq
  {n : ℤ}
-- given
  (hn : n < 0) :
-- imply
  invFact n = 0 := by
-- proof
  apply MetaMathlibExt.invFact_of_neg hn

/--
[invFact_natCast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma invFact_natCast_eq
  {n : ℕ} :
-- imply
  invFact n = (n.factorial : ℚ)⁻¹ := by
-- proof
  apply MetaMathlibExt.invFact_natCast n

/--
[invFact_shift](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma invFact_shift_eq
  {n : ℤ} :
-- imply
  invFact n = (n + 1) * invFact (n + 1) := by
-- proof
  apply MetaMathlibExt.invFact_shift n

/--
[intBinom_natCast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma intBinom_natCast_eq
  {n k : ℕ}
-- given
  (hk : k ≤ n) :
-- imply
  intBinom n k = n.choose k := by
-- proof
  apply MetaMathlibExt.intBinom_natCast hk

/--
[intBinom_of_neg_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma intBinom_of_neg_right_eq
  {n k : ℤ}
-- given
  (hk : k < 0) :
-- imply
  intBinom n k = 0 := by
-- proof
  apply MetaMathlibExt.intBinom_of_neg_right hk

/--
[intBinom_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma intBinom_of_lt_eq
  {n k : ℤ}
-- given
  (h : n < k) :
-- imply
  intBinom n k = 0 := by
-- proof
  apply MetaMathlibExt.intBinom_of_lt h

/--
[dixon_summation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_summation_eq
  {a₁ a₂ a₃ : ℤ} :
-- imply
  upsilon₃ a₁ a₂ a₃ =
    extFact (2 * a₁) * extFact (2 * a₂) * extFact (2 * a₃) *
    extFact (a₁ + a₂ + a₃) * invFact (a₁ + a₂) * invFact (a₁ + a₃) *
    invFact (a₂ + a₃) * invFact a₁ * invFact a₂ * invFact a₃ := by
-- proof
  apply MetaMathlibExt.dixon_summation a₁ a₂ a₃


-- created on 2026-10-20

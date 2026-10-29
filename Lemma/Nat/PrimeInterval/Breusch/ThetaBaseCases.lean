import Mathlib
import Initialize.Tactic.Attr.Basic
open Nat


namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[theta34_of_interval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/ThetaBaseCases.lean)
-/
@[path]
lemma theta34_of_interval
  {lo hi m : ℕ}
-- given
  (hlo : lo ≤ m)
  (hhi : m ≤ hi)
  (hend : 10 ^ lo * primorial hi ≤ 34 ^ lo) :
-- imply
  10 ^ m * primorial m ≤ 34 ^ m := by
-- proof
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hlo
  calc
    10 ^ (lo + k) * primorial (lo + k) ≤ 10 ^ (lo + k) * primorial hi := by
      exact Nat.mul_le_mul_left _ (primorial_mono hhi)
    _ = (10 ^ lo * primorial hi) * 10 ^ k := by
      simp only [pow_add]
      ac_rfl
    _ ≤ 34 ^ lo * 10 ^ k := Nat.mul_le_mul_right _ hend
    _ ≤ 34 ^ lo * 34 ^ k := by
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k)
    _ = 34 ^ (lo + k) := (pow_add 34 lo k).symm

-- These closed endpoint inequalities are evaluated once each instead of once per integer.
set_option exponentiation.threshold 2048
set_option maxRecDepth 16384
section

end

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[theta34_at_1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/ThetaBaseCases.lean)
-/
@[path]
lemma theta34_at_1 :
-- imply
  10 ^ 0 * primorial 1 ≤ 34 ^ 0 := by decide
end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[theta34_at_4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/ThetaBaseCases.lean)
-/
@[path]
lemma theta34_at_4 :
-- imply
  10 ^ 2 * primorial 4 ≤ 34 ^ 2 := by decide
end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[theta34_at_10](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/ThetaBaseCases.lean)
-/
@[path]
lemma theta34_at_10 :
-- imply
  10 ^ 5 * primorial 10 ≤ 34 ^ 5 := by decide
end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[theta34_at_18](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/ThetaBaseCases.lean)
-/
@[path]
lemma theta34_at_18 :
-- imply
  10 ^ 11 * primorial 18 ≤ 34 ^ 11 := by decide
end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[theta34_at_30](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/ThetaBaseCases.lean)
-/
@[path]
lemma theta34_at_30 :
-- imply
  10 ^ 19 * primorial 30 ≤ 34 ^ 19 := by decide
end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[theta34_at_46](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/ThetaBaseCases.lean)
-/
@[path]
lemma theta34_at_46 :
-- imply
  10 ^ 31 * primorial 46 ≤ 34 ^ 31 := by decide
end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[theta34_at_70](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/ThetaBaseCases.lean)
-/
@[path]
lemma theta34_at_70 :
-- imply
  10 ^ 47 * primorial 70 ≤ 34 ^ 47 := by decide
end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[theta34_at_100](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/ThetaBaseCases.lean)
-/
@[path]
lemma theta34_at_100 :
-- imply
  10 ^ 71 * primorial 100 ≤ 34 ^ 71 := by decide
end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[theta34_at_132](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/ThetaBaseCases.lean)
-/
@[path]
lemma theta34_at_132 :
-- imply
  10 ^ 101 * primorial 132 ≤ 34 ^ 101 := by
  set_option maxRecDepth 400000 in decide
end MathlibExt.NumberTheory.BreuschWanted.Internal


-- created on 2026-10-23
-- updated on 2026-10-28

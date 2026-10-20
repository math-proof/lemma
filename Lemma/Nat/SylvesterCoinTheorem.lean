import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.SylvesterCoinTheorem
open MetaMathlibExt


/--
[sylvester_coin_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterCoinTheorem.lean)
-/
@[path]
private lemma sylvester_coin_theorem_eq
  {a b : ℕ}
-- given
  (hab : Nat.Coprime a b) :
-- imply
  {n : ℕ | ¬ ∃ x y : ℕ, n = a * x + b * y}.ncard =
    (a - 1) * (b - 1) / 2 := by
-- proof
  apply MetaMathlibExt.sylvester_coin_theorem a b hab


-- created on 2026-10-20

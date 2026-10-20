import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.BangZsigmondy
open MetaMathlibExt


/--
[bangZsigmondy_exists_primitivePrimeDivisor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BangZsigmondy.lean)
-/
@[path]
private lemma bangZsigmondy_exists_primitivePrimeDivisor_eq
  {a b n : ℕ}
-- given
  (hbpos : 0 < b)
  (hba : b < a)
  (hcop : Nat.Coprime a b)
  (hn : 2 ≤ n)
  (hnexc : ¬ IsBangZsigmondyExceptional a b n) :
-- imply
  ∃ p, IntegerSequence.IsPrimitivePrimeDivisor
    (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n p := by
-- proof
  apply MetaMathlibExt.bangZsigmondy_exists_primitivePrimeDivisor hbpos hba hcop hn hnexc


-- created on 2026-10-20

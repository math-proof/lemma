import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.FermatResiduePeriod
open Nat


/--
[fermatNumber_mod_prime_exact_preperiod_period](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FermatResiduePeriod.lean)
-/
@[path]
private lemma fermatNumber_mod_prime_exact_preperiod_period_eq
  {p v w : ℕ}
-- given
  (hp : p.Prime)
  (hp2 : p ≠ 2)
  (hord : orderOf (2 : ZMod p) = 2 ^ v * w)
  (hw : Odd w) :
-- imply
  let k := by
-- proof
  apply Nat.fermatNumber_mod_prime_exact_preperiod_period p v w hp hp2 hord hw


-- created on 2026-10-20

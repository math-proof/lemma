import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeInterval.Breusch.Theta
open Nat Finset
open MathlibExt.NumberTheory.BreuschWanted.Internal


/--
[T03c_eqmain_margin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Theta.lean)
-/
@[path]
private lemma T03c_eqmain_margin_eq
  :
-- imply
  48 * (10 * Real.log 10 - 9 * Real.log 9) -
    (18900 / 279 + 18900 / 657 + 18900 / 963 : ℝ) * Real.log (34 / 10) > 13 := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.T03c_eqmain_margin

/--
[pi_third](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Theta.lean)
-/
@[path]
private lemma pi_third_eq
  {x : ℝ}
-- given
  (hx : 36 ≤ x) :
-- imply
  (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x / 3 := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.pi_third hx


-- created on 2026-10-20

import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeCounting.BrunTitchmarsh
open MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshWanted


/--
[brun_titchmarsh](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTitchmarsh.lean)
-/
@[path]
private lemma brun_titchmarsh_eq
  {X q a : ℕ}
-- given
  (haq : Nat.Coprime a q)
  (hq : 1 ≤ q)
  (hqX : q < X) :
-- imply
  (Nat.primeCountingMod X q a : ℝ) ≤
    2 * (X : ℝ) / ((Nat.totient q : ℝ) * Real.log ((X : ℝ) / (q : ℝ))) := by
-- proof
  apply MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshWanted.brun_titchmarsh X q a haq hq hqX


-- created on 2026-10-20

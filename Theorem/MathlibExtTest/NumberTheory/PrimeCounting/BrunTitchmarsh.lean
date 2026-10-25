/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PrimeCounting/BrunTitchmarsh.lean -/


import Def.NumberTheory.PrimeCounting.BrunTitchmarsh
import Lemma.Nat.PrimeCounting.BrunTitchmarsh
import Mathlib.Tactic.NormNum


namespace MathlibExtTest.NumberTheory.PrimeCounting.BrunTitchmarsh

open MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshWanted

-- Specialize the theorem to one nontrivial residue class.
example :
    (Nat.primeCountingMod 10 3 1 : ℝ) ≤
      2 * (10 : ℝ) / ((Nat.totient 3 : ℝ) * Real.log ((10 : ℝ) / 3)) := by
  exact brun_titchmarsh 10 3 1 (by norm_num) (by norm_num) (by norm_num)

-- For modulus one, recover the concrete prime-counting bound at ten.
example :
    (Nat.primeCounting 10 : ℝ) ≤ 2 * (10 : ℝ) / Real.log 10 := by
  simpa [Nat.primeCountingMod_one] using
    brun_titchmarsh 10 1 0 (by norm_num) (by norm_num) (by norm_num)

end MathlibExtTest.NumberTheory.PrimeCounting.BrunTitchmarsh

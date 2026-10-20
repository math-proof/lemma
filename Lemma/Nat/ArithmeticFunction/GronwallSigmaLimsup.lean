import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ArithmeticFunction.GronwallSigmaLimsup
open MathlibExt.NumberTheory.ArithmeticFunction.GronwallSigmaLimsupWanted


/--
[gronwall_sigma_limsup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/GronwallSigmaLimsup.lean)
-/
@[path]
private lemma gronwall_sigma_limsup_eq
  :
-- imply
  Filter.limsup
    (fun n : ℕ => ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
    ((n : ℝ) * Real.log (Real.log n))) Filter.atTop =
    Real.exp Real.eulerMascheroniConstant := by
-- proof
  apply MathlibExt.NumberTheory.ArithmeticFunction.GronwallSigmaLimsupWanted.gronwall_sigma_limsup


-- created on 2026-10-20

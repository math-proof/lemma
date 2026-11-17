module

public import Mathlib
public import Theorem.Analysis.SpecialFunctions.EntireExponentialIntegral

public section

open Set


namespace Complex

/--
[hasDerivAt_einTerm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/EntireExponentialIntegral.lean)
-/
public theorem hasDerivAt_einTerm_eq (n : ℕ) (z : ℂ) :
  HasDerivAt (einTerm n)
    ((-1 : ℂ) ^ n * z ^ n / ((n + 1).factorial : ℂ)) z :=
  hasDerivAt_einTerm n z

end Complex

namespace Complex

/--
[einTerm_deriv_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/EntireExponentialIntegral.lean)
-/
public theorem einTerm_deriv_norm_le_eq {R : ℝ} {z : ℂ}
  (hz : ‖z‖ < R) (n : ℕ) :
  ‖(-1 : ℂ) ^ n * z ^ n / ((n + 1).factorial : ℂ)‖ ≤
    R ^ n / n.factorial :=
  einTerm_deriv_norm_le hz n

end Complex

namespace Complex

/--
[EntireExponentialIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/EntireExponentialIntegral.lean)
-/
public theorem hasDerivAt_ein_eq
-- given
  (z : ℂ) :
-- imply
  HasDerivAt Complex.ein
    (∑' n : ℕ, (-1 : ℂ) ^ n * z ^ n / ((n + 1).factorial : ℂ)) z :=
-- proof
  hasDerivAt_ein z

end Complex

namespace Complex

/--
[EntireExponentialIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/EntireExponentialIntegral.lean)
-/
public theorem differentiable_ein_eq :
-- imply
  Differentiable ℂ Complex.ein :=
-- proof
  differentiable_ein

end Complex

namespace Complex

/--
[EntireExponentialIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/EntireExponentialIntegral.lean)
-/
public theorem analyticOnNhd_ein_eq :
-- imply
  AnalyticOnNhd ℂ Complex.ein Set.univ :=
-- proof
  analyticOnNhd_ein

end Complex

namespace Complex

/--
[exp_tail](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/EntireExponentialIntegral.lean)
-/
public theorem exp_tail_eq (z : ℂ) :
  (∑' n : ℕ, (-z) ^ (n + 1) / ((n + 1).factorial : ℂ)) =
    Complex.exp (-z) - 1 :=
  exp_tail z

end Complex

namespace Complex

/--
[EntireExponentialIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/EntireExponentialIntegral.lean)
-/
public theorem mul_deriv_ein_eq
-- given
  (z : ℂ) :
-- imply
  z * deriv Complex.ein z = 1 - Complex.exp (-z) :=
-- proof
  mul_deriv_ein z

end Complex


-- created on 2026-10-11
-- updated on 2026-10-26

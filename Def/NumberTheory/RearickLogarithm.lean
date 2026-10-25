/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RearickLogarithm.lean -/

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Tactic.IntervalCases
/-! Source: Rearick logarithm support characterization of multiplicative
arithmetic functions, after Huilan Li and Trueman MacHenry,
arXiv:1009.1892v1, <https://arxiv.org/abs/1009.1892>, lines 444-450
(Rearick logarithm definition) and 706-708 (Rearick Theorem 4). Real-valued
domain closure with `f 1 > 0` after Pong, arXiv:1504.03263v2,
<https://arxiv.org/abs/1504.03263>, lines 174-195; positivity also supplies
the nonzero premise for the Dirichlet inverse. -/


namespace MetaMathlibExt

set_option backward.proofsInPublic true in
/-- The Rearick logarithm of a real arithmetic function `f` with `0 < f 1`: it is `0` at `0`,
`Real.log (f 1)` at `1`, and `∑ d ∣ n, f d * f⁻¹ (n / d) * Real.log d` at `n > 1`, where `f⁻¹` is
the Dirichlet inverse of `f`. -/
noncomputable def rearickLog (f : ArithmeticFunction ℝ) (hf : 0 < f 1) :
    ArithmeticFunction ℝ :=
  ⟨fun n =>
    if n = 0 then 0
    else if n = 1 then Real.log (f 1)
    else
      ∑ d ∈ n.divisors,
        f d *
          ArithmeticFunction.dirichletInverse (⇑f)
            (invertibleOfNonzero (ne_of_gt hf)) (n / d) *
          Real.log (d : ℝ),
    by simp⟩

end MetaMathlibExt

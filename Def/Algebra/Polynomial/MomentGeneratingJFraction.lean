/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/MomentGeneratingJFraction.lean -/

import Mathlib.Data.Real.Basic
import Def.NumberTheory.HankelTransform
import Mathlib.Tactic.LinearCombination


namespace MetaMathlibExt

noncomputable def Jcoeff (α β : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | n, (k + 1) =>
    α n * Jcoeff α β n k +
      β (n + 1) * ∑ i : Fin k, Jcoeff α β (n + 1) (i.val) * Jcoeff α β n (k - 1 - i.val)
  termination_by _n k => k

end MetaMathlibExt

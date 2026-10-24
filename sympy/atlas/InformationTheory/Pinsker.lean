/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/Pinsker.lean -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Lemma.Real.LogSum
/-!
# Csiszar-Kullback-Pinsker inequality

For strictly positive probability vectors `p` and `q` on a finite type,
`(∑ |p a - q a|)² ≤ 2 * ∑ p a * log (p a / q a)`. The proof splits the type by the sign of
`p a - q a`, applies the log-sum inequality on each part, and reduces to the two-point case, which
is proved by calculus.
-/

open Finset BigOperators

namespace MathlibExt.InformationTheory.Pinsker

/-- The gap in the binary Pinsker inequality at `q`, for the reference point `v`. -/
private noncomputable def pinskerGap (v q : ℝ) : ℝ :=
  q * Real.log (q / v) + (1 - q) * Real.log ((1 - q) / (1 - v)) - 2 * (q - v) ^ 2

/-- The derivative of `pinskerGap v`. -/
private noncomputable def pinskerGapDeriv (v q : ℝ) : ℝ :=
  Real.log (q / v) - Real.log ((1 - q) / (1 - v)) - 4 * (q - v)
end MathlibExt.InformationTheory.Pinsker

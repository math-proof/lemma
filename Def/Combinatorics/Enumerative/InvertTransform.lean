/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/InvertTransform.lean -/

import Mathlib.RingTheory.PowerSeries.Inverse


namespace MetaMathlibExt

/-- INVERT transform of an integer sequence (concept `jis_sem_22fea8fd5a269c1828606fd8`;
source statements `jis_bdc94f3dcf45a8b11a488c9a`, `jis_fa06f78544747f9465a909ce`,
`jis_a1ec2137c84e5b9b5ce1f3f7`, `jis_dc5074e4bf1c7aedd3a999d3`).
Lean index `n` denotes source index `n+1` for both input and output.
The input ordinary generating function is embedded as `X * mk a`, whose constant
coefficient is zero, and the output is read off degrees `n+1` of the inverse of
`1 - X * mk a` obtained by `invOfUnit` with the unit `1` over `Int`. -/
noncomputable def invertTransform (a : ℕ → ℤ) : ℕ → ℤ :=
  fun n => PowerSeries.coeff (n + 1) ((1 - PowerSeries.X * PowerSeries.mk a).invOfUnit 1)

end MetaMathlibExt

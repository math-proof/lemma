import Lemma.Tensor.Interleave.eq.AppendStackS_Delta
import sympy.matrices.determinant
open Tensor


/--
Even/odd gather \(\boldsymbol{P}=\mathrm{interleave}\,d\) has determinant
\(\det\boldsymbol{P}=(-1)^{d/2}\) (Nat floor division).

Proof plan (row shift / induction): left-multiply by `ShiftMatrix(2d, d, 1)`
moves row `d` to index `1` with sign `(-1)^(d-1)`; the leading `2×2` is `I`
and the trailing block is `interleave (d-1)`, so
`det P_d = (-1)^(d-1) · det P_{d-1}`.
-/
@[main]
private lemma main
  {d : ℕ} :
-- imply
  (interleave d).det = (-1) ^ (d / 2) := by
-- proof
  sorry


-- created on 2026-09-07
-- updated on 2026-09-07

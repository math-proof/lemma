import sympy.functions.special.tensor_functions
import sympy.tensor.stack


def interleave (d : ℕ) : Tensor ℝ [d + d, d + d] :=
  ([i < d] [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * i)) : Tensor ℝ [])) ++
    ([i < d] [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * i + 1)) : Tensor ℝ []))


@[main]
private lemma main
-- given
  (d : ℕ) :
-- imply
  interleave d =
    ([i < d] [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * i)) : Tensor ℝ [])) ++
      ([i < d] [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * i + 1)) : Tensor ℝ [])) :=
-- proof
  rfl


-- created on 2026-09-04

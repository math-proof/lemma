import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.TripleFactorization
open MetaMathlibExt


/--
[triple_factorization_of_dot_diagram](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/TripleFactorization.lean)
-/
@[path]
private lemma triple_factorization_of_dot_diagram_eq
  {b : ℤ}
  {ε δ lam : ℝ}
  {g f : PowerSeries ℝ}
-- given
  (hg : PowerSeries.constantCoeff g = 1)
  (hf : PowerSeries.constantCoeff f = 0) :
-- imply
  let coeff := by
-- proof
  apply MetaMathlibExt.triple_factorization_of_dot_diagram b ε δ lam g f hg hf


-- created on 2026-10-20

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PQPatalanNumbers.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Cast.Order
/-!
# (p,q)-Patalan numbers

Formalization of the `(p,q)-Patalan numbers` concept.

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL18/Richardson/rich2.tex>.
-/


namespace MetaMathlibExt

/-- Generalized binomial coefficient with rational upper argument.

Auxiliary definition for the fractional-upper binomial appearing in the
`(p,q)-Patalan` definition. Stable source identifiers:
concept `jis_sem_46b7b4c899beee2d386fd944`,
statement `jis_64b108040f7dd4c159a901dc`,
source `jis_source_dcf0849efa23d51892aa79c7`. -/
def patalanGeneralizedBinomial (r : ℚ) (k : ℕ) : ℚ :=
  Finset.prod (Finset.range k) (fun i => r - (i : ℚ)) / (Nat.factorial k : ℚ)

end MetaMathlibExt

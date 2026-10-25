/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PQPatalanNumbers.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Cast.Order
import Def.Combinatorics.Enumerative.PQPatalanNumbers
/-!
# (p,q)-Patalan numbers

Formalization of the `(p,q)-Patalan numbers` concept.

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL18/Richardson/rich2.tex>.
-/


namespace MetaMathlibExt

/-- Admissible parameters for `(p,q)`-Patalan numbers: positive integers
`p` with `p > 1` and `q` with `0 < q < p`.

Bundling the bounds as fields of this structure makes the source restriction
part of the type of admissible parameters. Stable source identifiers:
concept `jis_sem_46b7b4c899beee2d386fd944`,
statement `jis_64b108040f7dd4c159a901dc`,
source `jis_source_dcf0849efa23d51892aa79c7`. -/
structure PQPatalanParams where
  p : ℕ
  q : ℕ
  hp : 1 < p
  hq_pos : 0 < q
  hq : q < p

end MetaMathlibExt

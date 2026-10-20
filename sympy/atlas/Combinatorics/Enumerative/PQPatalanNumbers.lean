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

/-- `(p,q)`-Patalan numbers: `b(n) = -p ^ (2 * n + 1) * binom{n - q / p}{n + 1}`.

The parameters are taken as a `PQPatalanParams` bundle, hence satisfy
`p > 1` and `0 < q < p`, and `n` is a natural number index. The binomial
factor uses a fractional upper argument. Stable source identifiers:
concept `jis_sem_46b7b4c899beee2d386fd944`,
statement `jis_64b108040f7dd4c159a901dc`,
source `jis_source_dcf0849efa23d51892aa79c7`. -/
def pqPatalanNumber (P : PQPatalanParams) (n : ℕ) : ℚ :=
  -((P.p : ℚ) ^ (2 * n + 1)) *
    patalanGeneralizedBinomial ((n : ℚ) - (P.q : ℚ) / (P.p : ℚ)) (n + 1)

end MetaMathlibExt

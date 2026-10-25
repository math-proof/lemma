/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PartitionPolynomial.lean -/

import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Combinatorics.Enumerative.Partition.Basic


namespace MetaMathlibExt

/-- Unnormalized partition polynomial `f_λ` (concept
`jis_term_a06e44e4f62cf3639dfdaa73`, source
`jis_source_4a49f53a6c92c67501cd5ea5`). -/
noncomputable def partitionPolynomial {n : ℕ} (lam : Nat.Partition n) :
    Polynomial ℕ :=
  (lam.parts.map fun a => (Polynomial.X : Polynomial ℕ) ^ a).sum

end MetaMathlibExt

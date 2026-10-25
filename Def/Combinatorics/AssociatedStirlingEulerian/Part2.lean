/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AssociatedStirlingEulerian.lean -/

import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Card
import Instance.Combinatorics.AssociatedStirlingEulerian


namespace MetaMathlibExt

/-- The `r`-minus-associated Stirling Eulerian number `A^(r-minus)_(n,m)`:
the cardinality of permutations of `n` objects with all cycle lengths at most
`r` and exactly `m` excedances.

Concept `jis_term_6573e30b9007548081ca6e28`; source JIS VOL28/Rakotoson/rakoto12.tex
Lines 257-259; URL https://cs.uwaterloo.ca/journals/JIS/VOL28/Rakotoson/rakoto12.tex. -/
def rMinusAssociatedStirlingEulerian (r n m : ℕ) : ℕ :=
  ((Finset.univ.filter (IsRMinusAssociatedCyclePerm r n)).filter
    (fun σ => excedanceCount n σ = m)).card

/-- The `r`-associated Stirling Eulerian number `A^r_(n,m)`: the cardinality of
permutations of `n` objects with all cycle lengths greater than `r` and exactly
`m` excedances.

Concept `jis_term_6573e30b9007548081ca6e28`; source JIS VOL28/Rakotoson/rakoto12.tex
Lines 653-657; URL https://cs.uwaterloo.ca/journals/JIS/VOL28/Rakotoson/rakoto12.tex. -/
def rAssociatedStirlingEulerian (r n m : ℕ) : ℕ :=
  ((Finset.univ.filter (IsRAssociatedCyclePerm r n)).filter
    (fun σ => excedanceCount n σ = m)).card

end MetaMathlibExt

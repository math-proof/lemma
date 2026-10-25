/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LegendreStirlingFirstKind.lean -/

import Def.Combinatorics.Enumerative.JacobiStirlingFirstKind
import Lemma.Finset.Enumerative.JacobiStirlingFirstKind


namespace MetaMathlibExt

/-- Generating polynomial for the Legendre-Stirling numbers of the first kind,
`∏ i ∈ Finset.range n, (X - i * (i + 1))` over `Polynomial ℤ`.
Concept `jis_sem_f66a64ccd0402d409b050315`, source equation `e:JacobiStirling1` /
`e:LeStirling` (statements `jis_01122ed9cc65cc42cecf4da1`,
`jis_073a5750ee8a25ebbba42d0c`). -/
noncomputable def legendreStirlingFirstPoly (n : ℕ) : Polynomial ℤ :=
  jacobiStirlingFirstPoly n (1 : ℤ)

/-- Legendre-Stirling number of the first kind `J(n, k; 1)`, defined as the
coefficient of `x ^ k` in the product over `i = 0, ..., n - 1` of
`(x - i * (i + 1))`.
Concept `jis_sem_f66a64ccd0402d409b050315` (statements
`jis_01122ed9cc65cc42cecf4da1`, `jis_073a5750ee8a25ebbba42d0c`). -/
noncomputable def legendreStirlingFirst (n k : ℕ) : ℤ :=
  jacobiStirlingFirst n k (1 : ℤ)

end MetaMathlibExt

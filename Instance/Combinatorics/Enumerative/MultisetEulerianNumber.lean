/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MultisetEulerianNumber.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Def.Combinatorics.Enumerative.MultisetEulerianNumber
/-!
# Eulerian numbers of multiset permutations

This file formalizes the descent-count definition in Dzhumadil'daev and
Yeliussizov, *Power Sums of Binomial Coefficients*:
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Yeliussizov/dzhuma6.tex>.
-/


namespace MetaMathlibExt

instance instDecidableIsMultisetPermutation {m K : ℕ} (k : Fin m → ℕ)
    (w : Fin K → Fin m) : Decidable (IsMultisetPermutation k w) :=
  inferInstanceAs (Decidable (∀ i,
    ((Finset.univ : Finset (Fin K)).filter fun j => w j = i).card = k i))

end MetaMathlibExt

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/RPRelation.lean -/

import Mathlib.Logic.Equiv.Basic
import Abbrev.Combinatorics.InfiniteWord.RPRelation


namespace MetaMathlibExt

namespace ReversePermute

/-- Reverse-permute (RP) relation on `k`-strings: `s` and `t` are related when
`t` can be obtained from `s` by permuting the entries (applying a permutation
of `Fin k` pointwise) and possibly reversing the string.
Cites concept `jis_sem_f50f75500661653b133949f3` (`rp relation`, alias
`RP relation`) and source statement `jis_cd98d66d9dff78260169a2e4`. -/
def rpRelation (k : ℕ) (s t : KString k) : Prop :=
  ∃ σ : Equiv.Perm (Fin k), t = s.map (⇑σ) ∨ t = s.reverse.map (⇑σ)

end ReversePermute
end MetaMathlibExt

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/RPRelation.lean -/

import Mathlib.Logic.Equiv.Basic


namespace MetaMathlibExt

namespace ReversePermute

/-- K-string: an ordered list of numbers from `[k]`, modelled as `List (Fin k)`.
Cites source statement `jis_cd98d66d9dff78260169a2e4` for concept
`jis_sem_f50f75500661653b133949f3` (`rp relation`, alias `RP relation`). -/
abbrev KString (k : ℕ) := List (Fin k)

end ReversePermute
end MetaMathlibExt

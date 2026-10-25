/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/EquilibriousWord.lean -/

import Mathlib.Data.List.Count


namespace MetaMathlibExt

/-- Finite binary word over the fixed alphabet `Sigma = {a, b}`, represented
canonically as `List (Fin 2)` with `0` and `1` the two letters. A word `u` is
equilibrious iff it contains equal numbers of `0`s and `1`s, counted with
`List.count`. Provenance: concept `jis_sem_061cc96760fa3a6b576dda00`,
source <https://cs.uwaterloo.ca/journals/JIS/VOL28/Coons/coons6.tex>, lines 543–575,
SHA-256 `409c8b4db7ce10e7f1cb6790bde41029c3667b383f6ccb05f6d374743bec2ff0`. -/
def IsEquilibriousWord (u : List (Fin 2)) : Prop :=
  u.count 0 = u.count 1

end MetaMathlibExt

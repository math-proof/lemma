import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry10ZetaSide
open MathlibExt.Analysis.Ramanujan.Part1Ch7
open Entry10Zeta4


/--
[meromorphicOn_chapter7Entry10ZetaSide](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry10ZetaSide.lean)
-/
@[path]
private lemma meromorphicOn_chapter7Entry10ZetaSide_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  MeromorphicOn (chapter7Entry10ZetaSide n) Set.univ := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry10Zeta4.meromorphicOn_chapter7Entry10ZetaSide n hn


-- created on 2026-10-20

import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.ExchangeConditionWiring
import Lemma.List.IsReduced_Drop.of.IsReduced
open List CoxeterGroup


/--
[isReduced_drop'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SignChangeExchangeFinal.lean)
-/
@[path]
private lemma main
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {word : List B}
  {j : ℕ}
-- given
  (hred : cs.IsReduced word) :
-- imply
  cs.IsReduced (word.drop j) :=
-- proof
  IsReduced_Drop.of.IsReduced (cs := cs) (word := word) (j := j) hred


-- created on 2026-10-23
-- updated on 2026-10-24

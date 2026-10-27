import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Formal


/--
[Formal.smul_eq_mul'](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {c:ℕ}
  {x:Formal} :
-- imply
  c • x = (c:Formal) * x :=
-- proof
  UnitsSystem.Formal.smul_eq_mul' c x


-- created on 2026-10-22

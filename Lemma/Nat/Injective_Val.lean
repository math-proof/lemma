import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.val_injective](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d : Dimensions} :
-- imply
  Function.Injective (Scalar.val (d := d)) :=
-- proof
  UnitsSystem.Scalar.val_injective d


-- created on 2026-10-22

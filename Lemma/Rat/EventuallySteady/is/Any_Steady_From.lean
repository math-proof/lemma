import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_1.Part9
open Rat


/--
[Rat.eventuallySteady_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_1.lean)
-/
@[path]
private lemma main
  {ε: ℚ}
  {a: Chapter5.Sequence} :
-- imply
  ε.EventuallySteady a ↔ ∃ N ≥ a.n₀, ε.Steady (a.from N) :=
-- proof
  Rat.eventuallySteady_def ε a


-- created on 2026-10-22

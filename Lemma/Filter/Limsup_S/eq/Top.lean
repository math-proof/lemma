import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.erdos_379.Part2
open Nat


/--
[erdos_379](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_379.lean)
-/
@[path]
private lemma main
  :
-- imply
  Filter.atTop.limsup (fun n ↦ (S n:ENat)) = ⊤ :=
-- proof
  erdos_379


-- created on 2026-10-22
